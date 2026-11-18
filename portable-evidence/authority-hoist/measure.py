import json,time,statistics,platform
from loaders import baseline as b,hoisted as h,batch
out={'schema':'authority-hoist-measurements/v1','python':platform.python_version(),'platform':platform.platform(),'clock':'perf_counter_ns','timed_region':'complete build, excluding synthetic fixture construction and output equality check','repetitions':9,'cases':{}}
for n in [1,100,1000]:
    a,raw=batch(n);expected=b.build(a,[raw]);samples={'baseline':[],'hoisted':[]}
    for fn in [b.build,h.build]:
        if fn(a,[raw])!=expected:raise ValueError('warmup mismatch')
    for rep in range(9):
        order=[('baseline',b.build),('hoisted',h.build)]
        if rep%2:order.reverse()
        for name,fn in order:
            t=time.perf_counter_ns();r=fn(a,[raw]);elapsed=time.perf_counter_ns()-t
            if r!=expected:raise ValueError('output mismatch')
            samples[name].append(elapsed)
    medians={k:statistics.median(v) for k,v in samples.items()}
    out['cases'][str(n)]={'records':n,'authority_sha256':b.digest(a),'source_sha256':b.hashlib.sha256(raw).hexdigest(),'projection_sha256':expected['projection_sha256'],'samples_ns':samples,'median_ns':medians,'ratio_baseline_over_hoisted':medians['baseline']/medians['hoisted'],'import_authority_digest_evaluations':{'baseline':n,'hoisted':1}}
print(json.dumps(out,indent=2,sort_keys=True))
