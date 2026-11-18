"""Independent receipt checker and descriptive (not inferential) ablation stats."""
import collections,hashlib,json,pathlib,random,statistics
ROOT=pathlib.Path(__file__).resolve().parent; OUT=ROOT/'ablation-results'
d=json.loads((OUT/'ablation.json').read_text()); plan=json.loads((OUT/'plan.json').read_text())
assert plan['seed']==d['seed']; rng=random.Random(d['seed']); orders=[]
for k in range(4):
    a=list(d['arms']); rng.shuffle(a); orders.append(a)
assert orders==d['round_order']==plan['order']
refs={}
for r in d['records']:
    if not r['reverse']: refs.setdefault(r['job'],r['witness'])
def outcome(w): return sorted(w['outcomes'],key=lambda x:(x['nodeid'],x['phase'],x['outcome'],str(x['skip_reason'])))
def qualifies(r,ref):
    w=r['witness']
    return r['returncode']==0 and w['exitstatus']==0 and sorted(w['items'])==sorted(ref['items']) and outcome(w)==outcome(ref)
assert len(d['records'])==64 and len(d['measurements'])==16
for r in d['records']:
    assert qualifies(r,refs[r['job']]),(r['label'],r['job'])
    ref=refs[r['job']]['items']; assert r['witness']['items']==(list(reversed(ref)) if r['reverse'] else ref)
    log=OUT/f"{r['label']}-{r['job']}.log"
    assert hashlib.sha256(log.read_bytes()).hexdigest()==r['stdout_sha256']
    assert json.loads((OUT/f"{r['label']}-{r['job']}.json").read_text())==r['witness']
for source in d['sources'].values(): assert source['tracked_status']==''
c0,c1=d['negative_control']; assert qualifies(c0,c0['witness'])
assert c1['returncode']==1 and not qualifies(c1,c0['witness'])
assert sorted(c0['witness']['items'])==sorted(c1['witness']['items'])
assert c1['witness']['items']==list(reversed(c0['witness']['items']))
assert any(o['outcome']=='failed' for o in c1['witness']['outcomes'])
ms={(m['round'],m['arm']):m['elapsed_ns'] for m in d['measurements']}
assert len(ms)==16 and [(m['round'],m['arm']) for m in d['measurements']]==[(i,a) for i,aa in enumerate(orders) for a in aa]
report={'checks':{'actual_job_runs':64,'same_ids_all_phases_skip_reasons':True,'reversal_verified':True,'raw_log_hashes_verified':True,'negative_order_control_rejected':True,'foreign_tracked_sources_unchanged':True},'arm_seconds':{},'paired_comparisons':{},'test_counts':{}}
for j,w in refs.items(): report['test_counts'][j]=dict(collections.Counter(o['outcome'] for o in w['outcomes'] if o['phase']=='call' or o['outcome']=='skipped'))
for arm in d['arms']:
    ts=[ms[k,arm]/1e9 for k in range(4)]; report['arm_seconds'][arm]={'rounds':ts,'median':statistics.median(ts),'minimum':min(ts),'maximum':max(ts)}
for base,new in [('O1','R1'),('O1','O2'),('O2','R2'),('R1','R2'),('O1','R2')]:
    reductions=[1-ms[k,new]/ms[k,base] for k in range(4)]
    report['paired_comparisons'][base+'->'+new]={'round_reductions':reductions,'median_paired_reduction':statistics.median(reductions),'ratio_of_medians_reduction':1/report['arm_seconds'][base]['median']*(report['arm_seconds'][base]['median']-report['arm_seconds'][new]['median']),'wins':sum(x>0 for x in reductions),'losses':sum(x<0 for x in reductions)}
(OUT/'summary.json').write_text(json.dumps(report,indent=2)); print(json.dumps(report,indent=2))
