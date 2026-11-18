"""Derive deterministic finite admission and Pareto decisions from observed receipts."""
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent; OUT=ROOT/'qualification-results'
d=json.loads((OUT/'ablation.json').read_text()); policy=json.loads((OUT/'policy.json').read_text())
assert list(d['arms'])==policy['candidate_ids'] and len(d['measurements'])==9 and len(d['records'])==36
baseline=policy['baseline']; measures={(m['round'],m['arm']):m for m in d['measurements']}
records={(int(r['label'].split('-')[1]),r['label'].split('-')[0],r['job']):r for r in d['records']}
def canon(w): return sorted(w['outcomes'],key=lambda x:(x['nodeid'],x['phase'],x['outcome'],str(x['skip_reason'])))
rows=[]
for candidate in policy['candidate_ids']:
    checks=[]; times=[]; caps=[]
    for k in range(policy['rounds']):
        elapsed=measures[k,candidate]['elapsed_ns']; cap=measures[k,baseline]['elapsed_ns']; times.append(elapsed);caps.append(cap)
        job_checks=[]
        for job in d['sources']:
            r=records[k,candidate,job]; b=records[k,baseline,job];w=r['witness'];bw=b['witness']
            raw=OUT/f"{r['label']}-{job}.log";assert hashlib.sha256(raw.read_bytes()).hexdigest()==r['stdout_sha256']
            assert json.loads((OUT/f"{r['label']}-{job}.json").read_text())==w
            ids=sorted(w['items'])==sorted(bw['items']); outcomes=canon(w)==canon(bw); exit_ok=r['returncode']==0 and w['exitstatus']==0
            job_checks.append({'job':job,'same_ids':ids,'same_phase_outcomes_skips':outcomes,'exit_zero':exit_ok})
        preservation=all(x['same_ids'] and x['same_phase_outcomes_skips'] and x['exit_zero'] for x in job_checks)
        checks.append({'round':k,'observed_preservation':preservation,'time_constraint':elapsed<=cap,'elapsed_ns':elapsed,'cap_ns':cap,'jobs':job_checks})
    admitted=all(c['observed_preservation'] and c['time_constraint'] for c in checks)
    rows.append({'id':candidate,'admitted':admitted,'empirical_preservation':all(c['observed_preservation'] for c in checks),'timing_ok':all(c['time_constraint'] for c in checks),'times_ns':times,'caps_ns':caps,'metrics':[max(times)],'worker_allocation':len(d['arms'][candidate]['queues']),'checks':checks,'rejections':[{'round':c['round'],'reason':'time_regression','excess_ns':c['elapsed_ns']-c['cap_ns']} for c in checks if not c['time_constraint']]})
def dominates(x,y):return all(a<=b for a,b in zip(x['metrics'],y['metrics'])) and any(a<b for a,b in zip(x['metrics'],y['metrics']))
frontier=[r for r in rows if r['admitted'] and not any(t['admitted'] and dominates(t,r) for t in rows)]
selected=min(frontier,key=lambda x:(x['metrics'],x['id']))
result={'policy_sha256':hashlib.sha256((OUT/'policy.json').read_bytes()).hexdigest(),'candidate_count':3,'candidates':rows,'frontier':[r['id'] for r in frontier],'selected':selected['id'],'scope':policy['scope']}
(OUT/'qualification.json').write_text(json.dumps(result,indent=2)); print(json.dumps({k:v for k,v in result.items() if k!='candidates'},indent=2))
for row in rows:print(row['id'],'admitted',row['admitted'],'metrics',row['metrics'],'rejections',row['rejections'])
