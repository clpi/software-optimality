from pathlib import Path
import sys
PIPELINE = Path(__file__).resolve().parent.parent/'pipeline'
sys.path.insert(0, str(PIPELINE))
import pipeline as baseline
import pipeline_hoisted as hoisted

def batch(n):
    context = dict(artifact='fixture-artifact',lineage='A',environment='lab',harness='ci-v1',workload='suite',venue='cpu')
    authority={'schema':'portable-authority/v1','context':context,'model':{'atoms':['passed','failed'],'edges':[],'events':[],'tasks':[],'horizon':0},'tests':{f'test{i}':{'pass':'passed','fail':'failed'} for i in range(n)},'benchmarks':{}}
    document={'schema':'ci-results/v1','context':context,'records':[{'subject':f'test{i}','status':'pass'} for i in range(n)]}
    return authority,baseline.canonical(document)
