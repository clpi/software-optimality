import concurrent.futures,hashlib,json,os,pathlib,platform,random,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parent; OUT=ROOT/'ablation-results'; OUT.mkdir(exist_ok=True)
PY=str(ROOT/'env/bin/python')
JOBS={'click':['tests/test_basic.py','tests/test_arguments.py'],'attrs':['tests/test_cmp.py','tests/test_converters.py'],'tomli':['tests/test_error.py','tests/test_misc.py'],'packaging':['tests/test_requirements.py','tests/test_errors.py']}
ARMS={'O1':{'reverse':False,'queues':[list(JOBS)]},'R1':{'reverse':True,'queues':[list(JOBS)]},'O2':{'reverse':False,'queues':[['packaging'],['tomli','attrs','click']]},'R2':{'reverse':True,'queues':[['packaging'],['tomli','attrs','click']]}}
SEED=20261118; ROUNDS=4; rng=random.Random(SEED)
plan=[]
for k in range(ROUNDS):
    arms=list(ARMS); rng.shuffle(arms); plan.append(arms)
(OUT/'plan.json').write_text(json.dumps({'seed':SEED,'rounds':ROUNDS,'arms':ARMS,'order':plan},indent=2))
def run(job,label,reverse=False,control=False):
    witness=OUT/f'{label}-{job}.json'; cwd=ROOT/('ablation-control' if control else job)
    env=dict(os.environ,PYTHONPATH=str(ROOT),WITNESS_PATH=str(witness),REVERSE_TESTS=str(int(reverse)),PYTHONHASHSEED='0',PYTEST_DISABLE_PLUGIN_AUTOLOAD='1')
    cmd=[PY,'-m','pytest','-q','-p','ablation_witness','-o','addopts=','--basetemp',str(OUT/f'tmp-{label}-{job}'),*(['test_order_dependency.py'] if control else JOBS[job])]
    start=time.perf_counter_ns(); p=subprocess.run(cmd,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT); end=time.perf_counter_ns()
    (OUT/f'{label}-{job}.log').write_bytes(p.stdout)
    return {'job':job,'label':label,'reverse':reverse,'elapsed_ns':end-start,'returncode':p.returncode,'command':cmd,'stdout_sha256':hashlib.sha256(p.stdout).hexdigest(),'witness':json.loads(witness.read_text()) if witness.exists() else None}
records=[]; measurements=[]
for k,arm_order in enumerate(plan):
    for arm in arm_order:
        cfg=ARMS[arm]
        def worker(q): return [run(j,f'{arm}-{k}',cfg['reverse']) for j in q]
        start=time.perf_counter_ns()
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(cfg['queues'])) as pool: batches=list(pool.map(worker,cfg['queues']))
        elapsed=time.perf_counter_ns()-start; rs=sum(batches,[]); records.extend(rs)
        measurements.append({'round':k,'arm':arm,'elapsed_ns':elapsed,'returncodes':[r['returncode'] for r in rs]})
        print(k,arm,elapsed,[r['returncode'] for r in rs],flush=True)
        (OUT/'partial.json').write_text(json.dumps({'measurements':measurements,'records':records}))
controls=[run('control','negative-original',False,True),run('control','negative-reversed',True,True)]
manifest={'seed':SEED,'round_order':plan,'arms':ARMS,'measurements':measurements,'records':records,'negative_control':controls,'python':platform.python_version(),'platform':platform.platform(),'sources':{j:{'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT/j,text=True).strip(),'remote':subprocess.check_output(['git','remote','get-url','origin'],cwd=ROOT/j,text=True).strip(),'tracked_status':subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=ROOT/j,text=True).strip(),'tests':JOBS[j]} for j in JOBS}}
(OUT/'ablation.json').write_text(json.dumps(manifest,indent=2)); print('COMPLETE',flush=True)
