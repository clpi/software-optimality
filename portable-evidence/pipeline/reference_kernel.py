#!/usr/bin/env python3
"""Exact reference for the declared finite, fixed-duration schedule model."""
import argparse, hashlib, itertools, json

def unique_object(pairs):
    result={}
    for key,value in pairs:
        if key in result: raise ValueError('duplicate JSON key: '+key)
        result[key]=value
    return result

def parse_json(text):
    return json.loads(text,object_pairs_hook=unique_object)

def read_json(path):
    with open(path) as stream: return parse_json(stream.read())

def digest(x):
    return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def matches(requirements, context):
    return all(context.get(k)==v for k,v in requirements.items())

def derive(spec, context):
    """Least supported closure. A cycle cannot create its own support."""
    withdrawn={e['target'] for e in spec['events'] if e['type']=='withdraw'}
    live=[e for e in spec['events'] if e['type']=='observe' and e['id'] not in withdrawn and matches(e.get('context',{}),context)]
    support={}
    for e in live: support.setdefault(e['atom'],set()).add(e['id'])
    edges=sorted((e for e in spec['edges'] if e['id'] not in withdrawn and matches(e.get('context',{}),context)),key=lambda e:e['id'])
    steps=[]
    changed=True
    while changed:
        changed=False
        for e in edges:
            if all(p in support for p in e['premises']) and e['conclusion'] not in support:
                support[e['conclusion']]=set().union(*(support[p] for p in e['premises']))|{e['id']}
                steps.append(e['id']); changed=True
    def status(item):
        pos=item.get('positive') in support; neg=item.get('negative') in support
        return 'conflict' if pos and neg else 'qualified' if pos else 'refuted' if neg else 'unsupported'
    return {'observed':sorted({e['atom'] for e in live}), 'derived':sorted(support),
            'support_paths':{k:sorted(v) for k,v in sorted(support.items())},'derivation_steps':steps,
            'capabilities':{i['id']:status(i) for i in spec.get('capabilities',[])},
            'intents':{i['id']:status(i) for i in spec.get('intents',[])}}

def incidence(spec):
    # Separate channels preserve tail/head identity even for self-loops.
    return {a:{e['id']:{'tail_positions':[i for i,p in enumerate(e['premises']) if p==a],
                        'head':e['conclusion']==a} for e in spec['edges']} for a in spec['atoms']}

def schedules(spec,context):
    """All integer-start schedules within the declared horizon, including idle ties."""
    horizon=spec['horizon']
    tasks=[t for t in spec['tasks'] if matches(t.get('context',{}),context)]
    result={}
    choices=[]
    for t in tasks:
        choices.append([None]+[(v,start,start+d) for v,d in sorted(t['duration'].items())
                               for start in range(horizon-d+1)])
    for placements in itertools.product(*choices):
        placed={t['id']:(t,p) for t,p in zip(tasks,placements) if p is not None}
        valid=True
        for tid,(t,p) in placed.items():
            for dep in t.get('requires',[]):
                if dep not in placed or placed[dep][1][2]>p[1]: valid=False
        for (ta,pa),(tb,pb) in itertools.combinations(placed.values(),2):
            exclusive=pa[0]==pb[0] or bool(set(ta.get('resources',[])) & set(tb.get('resources',[])))
            if exclusive and not (pa[2]<=pb[1] or pb[2]<=pa[1]): valid=False
        if not valid: continue
        timeline=[{'task':tid,'venue':p[0],'start':p[1],'end':p[2]} for tid,(t,p) in sorted(placed.items())]
        coverage=sorted(set().union(*(set(t['covers']) for t,p in placed.values())))
        candidate={'timeline':timeline,'coverage':coverage,'makespan':max((p[2] for t,p in placed.values()),default=0)}
        result[digest(candidate)]=candidate
    return dict(sorted(result.items()))

def dominates(a,b):
    ca,cb=set(a['coverage']),set(b['coverage'])
    return ca>=cb and a['makespan']<=b['makespan'] and (ca!=cb or a['makespan']<b['makespan'])

def solve(spec,context):
    validate(spec); validate_context(context)
    candidates=schedules(spec,context)
    frontier=[i for i,b in candidates.items() if not any(dominates(a,b) for a in candidates.values())]
    return {'schema':'hyper-reference/v1','input_hash':digest(spec),'context':context,
            'measurement_kind':'declared fixture durations, NOT measured execution',
            'views':derive(spec,context),'incidence':incidence(spec),
            'candidates':candidates,'frontier':frontier}

def require(condition, message):
    if not condition: raise ValueError(message)

def fields(obj, required, optional=()):
    require(type(obj) is dict, 'object required')
    require(set(required)<=obj.keys() and obj.keys()<=set(required)|set(optional),
            'missing or unsupported fields: '+str(obj.keys()))

def names(xs):
    require(type(xs) is list and all(type(x) is str and x for x in xs), 'nonempty string list required')
    require(len(set(xs))==len(xs), 'duplicate names')

def validate_context(context):
    require(type(context) is dict and set(context)<={'lineage','environment'}, 'unsupported context selector')
    require(all(type(v) is str and v for v in context.values()), 'context values must be nonempty strings')

def validate(spec):
    fields(spec, ['atoms','edges','events','tasks','horizon'], ['capabilities','intents'])
    require(type(spec['horizon'])==int and spec['horizon']>=0, 'horizon must be a nonnegative integer')
    names(spec['atoms']); atoms=set(spec['atoms'])
    for key in ('edges','events','tasks','capabilities','intents'):
        require(type(spec.get(key,[])) is list, key+' must be a list')
    for e in spec['edges']:
        fields(e,['id','premises','conclusion'],['context'])
        names([e['id']]); names(e['premises'])
        require(type(e['conclusion']) is str and set(e['premises'])|{e['conclusion']}<=atoms, 'dangling edge atom')
        validate_context(e.get('context',{}))
    for e in spec['events']:
        require(type(e) is dict and e.get('type') in ('observe','withdraw'), 'unsupported event')
        if e['type']=='observe':
            fields(e,['id','type','atom'],['context']); validate_context(e.get('context',{}))
            require(type(e['atom']) is str and e['atom'] in atoms, 'dangling observation atom')
        else: fields(e,['id','type','target'])
        names([e['id']])
    names([e['id'] for e in spec['edges']+spec['events']])
    targets={e['id'] for e in spec['edges']}|{e['id'] for e in spec['events'] if e['type']=='observe'}
    for e in spec['events']:
        if e['type']=='withdraw':
            require(type(e['target']) is str and e['target'] in targets,'unknown withdrawal target')
    for key in ('capabilities','intents'):
        items=spec.get(key,[])
        for i in items:
            fields(i,['id','positive'],['negative']); names([i['id']])
            require(type(i['positive']) is str and i['positive'] in atoms,'dangling positive qualification')
            if 'negative' in i: require(type(i['negative']) is str and i['negative'] in atoms,'dangling negative qualification')
        names([i['id'] for i in items])
    for t in spec['tasks']:
        fields(t,['id','kind','covers','duration'],['requires','resources','context'])
        names([t['id']]);names(t['covers']);names(t.get('requires',[]));names(t.get('resources',[]))
        validate_context(t.get('context',{}))
        require(t['kind'] in ('test','benchmark','fuzz'),'unsupported task kind')
        require(set(t['covers'])<=atoms,'dangling coverage target')
        require(type(t['duration']) is dict and bool(t['duration']), 'duration map required')
        names(list(t['duration']))
        require(all(type(d)==int and d>0 for d in t['duration'].values()),'durations must be positive integers')
    names([t['id'] for t in spec['tasks']]); ids={t['id'] for t in spec['tasks']}
    for t in spec['tasks']: require(set(t.get('requires',[]))<=ids,'dangling task prerequisite')

def main():
    p=argparse.ArgumentParser(); p.add_argument('spec'); p.add_argument('--context',default='{}'); p.add_argument('--check')
    args=p.parse_args(); spec=read_json(args.spec);validate(spec)
    output=solve(spec,parse_json(args.context))
    if args.check:
        require(read_json(args.check)==output, 'receipt differs from exhaustive recomputation')
        print('receipt matches exact recomputation')
    else: print(json.dumps(output,sort_keys=True,indent=2))
if __name__=='__main__': main()
