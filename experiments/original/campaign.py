import concurrent.futures, hashlib, itertools, json, os, pathlib, platform, statistics, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parent
PY=str(ROOT/'env/bin/python')
JOBS={'click':['tests/test_basic.py','tests/test_arguments.py'], 'attrs':['tests/test_cmp.py','tests/test_converters.py'], 'tomli':['tests/test_error.py','tests/test_misc.py'], 'packaging':['tests/test_requirements.py','tests/test_errors.py']}
OUT=ROOT/'results'; OUT.mkdir(exist_ok=True)
def run(job,label,reverse=False):
    witness=OUT/f'{label}-{job}.json'
    env=dict(os.environ,PYTHONPATH=str(ROOT),WITNESS_PATH=str(witness),REVERSE_TESTS=str(int(reverse)),PYTHONHASHSEED='0',PYTEST_DISABLE_PLUGIN_AUTOLOAD='1')
    cmd=[PY,'-m','pytest','-q','-p','witness_plugin','-o','addopts=','--basetemp',str(OUT/f'tmp-{label}-{job}'),*JOBS[job]]
    start=time.perf_counter_ns(); p=subprocess.run(cmd,cwd=ROOT/job,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT); ns=time.perf_counter_ns()-start
    (OUT/f'{label}-{job}.log').write_bytes(p.stdout)
    r={'job':job,'label':label,'reverse':reverse,'elapsed_ns':ns,'returncode':p.returncode,'command':cmd,'stdout_sha256':hashlib.sha256(p.stdout).hexdigest()}
    if witness.exists(): r['witness']=json.loads(witness.read_text())
    return r
records=[]
for k in range(3):
    for job in JOBS:
        r=run(job,f'profile{k}'); records.append(r); print(job,k,r['returncode'],r['elapsed_ns'],flush=True)
        if r['returncode']!=0:
            (OUT/'partial.json').write_text(json.dumps(records,indent=2)); raise SystemExit('Test job failed; inspect logs')
cost={j:int(statistics.median(r['elapsed_ns'] for r in records if r['job']==j)) for j in JOBS}
candidates=[]
for perm in itertools.permutations(JOBS):
    for cut in range(5):
        queues=[list(perm[:cut]),list(perm[cut:])]
        finish=[]
        for q in queues:
            acc=0
            for j in q: acc+=cost[j]; finish.append(acc)
        candidates.append({'queues':queues,'metrics':[max(sum(cost[j] for j in q) for q in queues),sum(finish)]})
def dom(a,b): return all(x<=y for x,y in zip(a,b)) and any(x<y for x,y in zip(a,b))
frontier=[c for c in candidates if not any(dom(d['metrics'],c['metrics']) for d in candidates)]
chosen=min(frontier,key=lambda c:(c['metrics'],c['queues']))
schedules={'baseline':[list(JOBS),[]],'optimized':chosen['queues']}
measurements=[]
for k in range(3):
    for name in (['baseline','optimized'] if k%2==0 else ['optimized','baseline']):
        def worker(q): return [run(j,f'{name}{k}',name=='optimized') for j in q]
        start=time.perf_counter_ns()
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool: batches=list(pool.map(worker,schedules[name]))
        elapsed=time.perf_counter_ns()-start
        rs=sum(batches,[]); records.extend(rs)
        measurements.append({'round':k,'schedule':name,'elapsed_ns':elapsed,'returncodes':[r['returncode'] for r in rs]})
        print(name,k,elapsed,flush=True)
reference={r['job']:r['witness'] for r in records if r['label']=='profile0'}
checks=[]
for r in records:
    w=r.get('witness',{}); ref=reference[r['job']]
    checks.append({'label':r['label'],'job':r['job'],'same_test_ids':sorted(w.get('items',[]))==sorted(ref['items']),'same_outcomes':sorted(w.get('outcomes',[]))==sorted(ref['outcomes']),'success':r['returncode']==0})
manifest={'sources':{j:{'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT/j,text=True).strip(),'remote':subprocess.check_output(['git','remote','get-url','origin'],cwd=ROOT/j,text=True).strip(),'tests':JOBS[j]} for j in JOBS},'python':platform.python_version(),'platform':platform.platform(),'venues':'two logical local subprocess workers on same host; not remote venues','cost_ns':cost,'candidate_count':len(candidates),'frontier':frontier,'chosen':chosen,'candidates':candidates,'measurements':measurements,'checks':checks,'records':records}
(OUT/'campaign.json').write_text(json.dumps(manifest,indent=2))
print('RESULT',len(candidates),'frontier',len(frontier),'checks',all(all(c[k] for k in ['same_test_ids','same_outcomes','success']) for c in checks))
