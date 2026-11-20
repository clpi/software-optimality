import hashlib,json,platform,statistics,time
from pathlib import Path
import replay
p=replay.pipeline
FIX=Path(p.__file__).parent/'fixtures'
a=json.loads((FIX/'authority.json').read_text());raw=(FIX/'ci.json').read_bytes()
workloads={'replayed_1000':[raw]*1000,'unique_100':[raw+b' '*i for i in range(100)],'mixed_1000':[raw+b' '*(i%10) for i in range(1000)]}
result={'schema':'replay-measurements/v1','python':platform.python_version(),'platform':platform.platform(),'clock':'perf_counter_ns','repetitions':9,'timed_region':'complete build, excluding input construction and equality check','cases':{}}
for name,sources in workloads.items():
    expected=p.build(a,sources)
    if replay.build(a,sources)!=expected:raise ValueError('projection mismatch')
    for fn in [p.build,replay.build]:fn(a,sources)
    samples={'baseline':[],'deduplicated':[]}
    for i in range(9):
        order=[('baseline',p.build),('deduplicated',replay.build)]
        if i%2:order.reverse()
        for key,fn in order:
            start=time.perf_counter_ns();actual=fn(a,sources);elapsed=time.perf_counter_ns()-start
            if actual!=expected:raise ValueError('timed output mismatch')
            samples[key].append(elapsed)
    case={'deliveries':len(sources),'distinct_byte_documents':len(set(sources)),'samples_ns':samples,'projection_sha256':expected['projection_sha256'],'logical_import_calls':{'baseline':len(sources),'deduplicated':len(set(sources))}}
    case['median_ns']={k:statistics.median(v) for k,v in samples.items()}
    case['median_ratio_baseline_over_deduplicated']=case['median_ns']['baseline']/case['median_ns']['deduplicated']
    result['cases'][name]=case
print(json.dumps(result,indent=2,sort_keys=True))
