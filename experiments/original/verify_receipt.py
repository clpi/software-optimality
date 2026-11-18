"""Independent exhaustive assignment/queue enumerator and receipt checks."""
import itertools,json,pathlib
p=pathlib.Path(__file__).parent/'results/campaign.json'; d=json.loads(p.read_text())
jobs=list(d['sources']); costs=d['cost_ns']
actual={tuple(tuple(q) for q in c['queues']) for c in d['candidates']}
expected=set()
for assignment in itertools.product(range(2),repeat=len(jobs)):
    partitions=[[j for j,v in zip(jobs,assignment) if v==k] for k in range(2)]
    for queues in itertools.product(*(itertools.permutations(q) for q in partitions)): expected.add(queues)
assert len(actual)==len(d['candidates'])==len(expected)==120 and actual==expected
metrics={}
for qs in expected:
    sums=[0,0]; total_completion=0
    for v,q in enumerate(qs):
        for job in q: sums[v]+=costs[job]; total_completion+=sums[v]
    metrics[qs]=(max(sums),total_completion)
for c in d['candidates']: assert tuple(c['metrics'])==metrics[tuple(map(tuple,c['queues']))]
frontier={q for q,m in metrics.items() if not any(all(a<=b for a,b in zip(n,m)) and any(a<b for a,b in zip(n,m)) for n in metrics.values())}
assert frontier=={tuple(map(tuple,c['queues'])) for c in d['frontier']}
assert tuple(map(tuple,d['chosen']['queues'])) in frontier
refs={r['job']:r['witness'] for r in d['records'] if r['label']=='profile0'}
for r in d['records']:
    assert r['returncode']==0
    assert sorted(r['witness']['items'])==sorted(refs[r['job']]['items'])
    assert sorted(r['witness']['outcomes'])==sorted(refs[r['job']]['outcomes'])
    if r['reverse']: assert r['witness']['items']==list(reversed(refs[r['job']]['items']))
print('PASS: 120 unique schedules; independent exhaustive enumeration agrees; metric/frontier exact; all node IDs and observed outcomes preserved; reverse collection confirmed.')
