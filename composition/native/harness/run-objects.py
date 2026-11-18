from pathlib import Path
import subprocess, json, hashlib, time, os, signal, shutil, re

base = Path('/workspace/home/identity')
repo = base / 'idol'
art = base / 'artifacts'
out = base / 'results-objects'
out.mkdir(exist_ok=True)
seed = art / 'idol-seed'
expiry = 1795003709
records = []
cases = []

def sha(path):
    return hashlib.file_digest(path.open('rb'), 'sha256').hexdigest()

def artifact(path):
    with path.open('rb') as f:
        head = f.read(20)
    info = {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path),
            'elf_machine': int.from_bytes(head[18:20], 'little') if head[:4] == b'\x7fELF' else None,
            'elf_type': int.from_bytes(head[16:18], 'little') if head[:4] == b'\x7fELF' else None}
    return info

def invoke(name, args, cwd, limit, env=None):
    remaining = int(expiry - time.time() - 180)
    if remaining <= 0:
        raise RuntimeError('Preserving three minutes to retain receipts and delete sandbox')
    limit = min(limit, remaining)
    log = out / (name + '.log')
    start = time.monotonic()
    with log.open('wb') as stream:
        proc = subprocess.Popen([str(x) for x in args], cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        timedout = False
        try:
            code = proc.wait(timeout=limit)
        except subprocess.TimeoutExpired:
            timedout = True
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                code = proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                code = proc.wait()
    data = log.read_bytes()
    record = {'name': name, 'command': [str(x) for x in args], 'cwd': str(cwd),
              'environment_overrides': {'TMPDIR': env['TMPDIR']} if env and 'TMPDIR' in env else {},
              'exit': code, 'timeout': timedout, 'timeout_seconds': limit,
              'seconds': time.monotonic() - start, 'log_sha256': hashlib.sha256(data).hexdigest(),
              'bytes': len(data), 'output': data.decode(errors='replace')}
    records.append(record)
    (out / (name + '.json')).write_text(json.dumps(record, indent=2) + '\n')
    (out / 'runs.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps({k:v for k,v in record.items() if k not in ['output','command']}), flush=True)
    return record

def run_case(label, source, cwd, expected=None):
    scratch = base / ('scratch-' + label)
    scratch.mkdir()  # no prior outputs can enter this case
    env = dict(os.environ, TMPDIR=str(scratch))
    obj = art / (label + '.o')
    binary = art / (label + '.native')
    case = {'label': label, 'source': source, 'source_sha256': sha(cwd/source),
            'compiler_sha256': sha(seed), 'expected_assertions': expected, 'scratch': str(scratch)}
    cases.append(case)
    compile_result = invoke(label+'-compile', [seed, 'compile', '--no-cache', '--backend=direct',
        '--target', 'native-exe', '--emit', 'obj', source, '-o', obj], cwd, 240, env)
    case['compile_exit'] = compile_result['exit']
    if compile_result['exit'] != 0:
        case['verdict'] = 'compile_refused_before_assertions'
        return
    inputs = [art/'start.o', obj]
    logical = [('keyword_classify.o', 'keyword.o'), ('idol_io_runtime.o','io.o'),
               ('idol_str_runtime.o','str.o'), ('idol_errno_runtime.o','errno.o')]
    selected = []
    for original, runtime in logical:
        placeholders = list(scratch.glob('idol-boot-*-'+original))
        if placeholders:
            assert len(placeholders)==1 and placeholders[0].stat().st_size==0
            selected.append({'logical': original, 'placeholder': str(placeholders[0]), 'actual': str(art/runtime)})
            inputs.append(art/runtime)
    homes = sorted(scratch.glob('idol-home-*.o'))
    inputs.extend(homes)
    case['selected_bootstrap_units'] = selected
    case['inputs'] = [artifact(p) for p in inputs]
    assert all(a['elf_machine']==183 and a['elf_type']==1 for a in case['inputs'])
    args = ['ld','-m','aarch64linux','-o',binary,'--dynamic-linker','/lib/ld-linux-aarch64.so.1',
            '--eh-frame-hdr','--hash-style=gnu','--build-id']
    for p in ['/usr/lib/aarch64-linux-gnu','/lib/aarch64-linux-gnu','/usr/lib64','/lib64','/usr/lib','/lib','/usr/lib/gcc/aarch64-linux-gnu/14']:
        args.append('-L'+p)
    args += inputs + ['--gc-sections','-lm','-lgcc','--push-state','--as-needed','-lgcc_s','--pop-state',
                      '-lc','-lgcc','--push-state','--as-needed','-lgcc_s','--pop-state']
    linked = invoke(label+'-link', args, cwd, 30)
    case['link_exit'] = linked['exit']
    if linked['exit'] != 0:
        case['verdict'] = 'link_refused_before_assertions'
        return
    case['artifact'] = artifact(binary)
    assert case['artifact']['elf_machine']==183 and case['artifact']['elf_type'] in [2,3]
    run = invoke(label+'-native',[binary],cwd,120)
    case['native_exit'] = run['exit']
    lines = run['output'].splitlines()
    case['pass_lines'] = sum(x.startswith('PASS ') for x in lines)
    case['fail_lines'] = sum(x.startswith('FAIL ') for x in lines)
    case['assertion_lines'] = case['pass_lines'] + case['fail_lines']
    case['failure_summaries'] = [int(v) for v in re.findall(r'^failures=(\d+)$',run['output'],re.M)]
    case['control_summaries'] = re.findall(r'^controls=(\d+) fails=(\d+)$',run['output'],re.M)
    complete = expected is None or case['assertion_lines']==expected
    clean = case['failure_summaries']==[0] if expected is not None else len(case['control_summaries'])==1 and case['control_summaries'][0][1]=='0'
    case['verdict'] = 'pass' if run['exit']==0 and complete and clean and case['fail_lines']==0 else 'executed_assertion_failure_or_incomplete'

try:
    seed_info = artifact(seed)
    assert seed_info['elf_machine']==183 and seed_info['bytes']>0
    (out/'seed.json').write_text(json.dumps(seed_info,indent=2)+'\n')
    run_case('identity','test/compiler/identity.id',repo,58)
    (out/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    baseline = base/'baseline-repo'
    shutil.copytree(repo,baseline,ignore=shutil.ignore_patterns('.zig-cache','zig-out','.cache','.git'),dirs_exist_ok=True)
    owners = []
    for name in ['effect.id','graph.id']:
        path = Path('lib/compiler')/name
        before = sha(baseline/path)
        (baseline/path).write_bytes((base/'baseline'/path).read_bytes())
        owners.append({'path':str(path),'candidate_sha256':before,'baseline_sha256':sha(baseline/path)})
    assert sha(repo/'test/compiler/identity.id')==sha(baseline/'test/compiler/identity.id')
    (out/'ablation.json').write_text(json.dumps({'candidate_commit':'ef3dbcfa847579df2c839bb73240242fe5ebdd4e',
        'baseline_commit':'fcb056649dd63dcd58dec32602917ebfcbf44bc9','owners':owners,
        'test_sha256':sha(repo/'test/compiler/identity.id'),'compiler_sha256':sha(seed)},indent=2)+'\n')
    run_case('identity-ablation','test/compiler/identity.id',baseline,58)
    (out/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    for label,path,count in [('topology','test/compiler/topology.id',13),
        ('effects','lib/compiler/self/host/tests/effects.id',None),
        ('graph','lib/compiler/self/host/tests/graph.id',None),
        ('policy','lib/compiler/self/host/tests/policy.id',None),
        ('policycone','lib/compiler/self/host/tests/policycone.id',None)]:
        if time.time()>expiry-(210 if label=='topology' else 360):
            cases.append({'label':label,'verdict':'not_run_preserve_receipt_and_cleanup_margin'})
            continue
        run_case(label,path,repo,count)
        (out/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    (out/'completed.json').write_text(json.dumps({'status':'COMPLETED','cases':len(cases)})+'\n')
except Exception as e:
    (out/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    (out/'completed.json').write_text(json.dumps({'status':'FAILED','reason':repr(e)})+'\n')
    raise
