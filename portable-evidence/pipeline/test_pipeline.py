import copy
import json
from pathlib import Path
import unittest
import pipeline as p

class PipelineTest(unittest.TestCase):
    def setUp(self):
        self.a=json.loads(Path('fixtures/authority.json').read_text())
        self.ci=Path('fixtures/ci.json').read_bytes()
        self.bench=Path('fixtures/benchmark.json').read_bytes()
    def raw(self, **kw):
        d=json.loads(self.ci); d.update(kw); return json.dumps(d).encode()
    def test_e2e(self):
        r=p.build(self.a,[self.ci,self.bench]); v=r['inferred_view']
        self.assertEqual(len(r['observed_receipts']),2)
        self.assertNotIn('observed_suite',v['observed'])
        self.assertIn('observed_suite',v['derived'])
        self.assertEqual(v['intents']['receipt-completeness'],'qualified')
        self.assertEqual(r['proposed_tasks'][0]['id'],'rerun')
    def test_order_and_duplicate_idempotence(self):
        self.assertEqual(p.build(self.a,[self.ci,self.bench]),p.build(self.a,[self.bench,self.ci,self.ci]))
    def test_context_each_field(self):
        for k in p.CONTEXT:
            c=self.a['context'].copy();c[k]+='-other'
            with self.assertRaises(ValueError):p.build(self.a,[self.raw(context=c)])
    def test_no_policy_submission(self):
        with self.assertRaises(ValueError): p.build(self.a,[self.raw(policy={'allow':True})])
    def test_unknown_subject(self):
        with self.assertRaises(ValueError): p.build(self.a,[self.raw(records=[{'subject':'foreign','status':'pass'}])])
    def test_nonpass_preserved_not_support(self):
        for status in ['skipped','error']:
            r=p.build(self.a,[self.raw(records=[{'subject':'checkout','status':status}])])
            self.assertEqual(len(r['observed_receipts']),1)
            self.assertEqual(r['inferred_view']['observed'],[])
    def test_conflict(self):
        failed=self.raw(records=[{'subject':'checkout','status':'fail'}])
        r=p.build(self.a,[self.ci,failed]);self.assertEqual(r['inferred_view']['capabilities']['checkout-case'],'conflict')
    def test_withdraw_retracts_downstream(self):
        rid=p.import_document(self.a,self.ci)[0]['id']
        r=p.build(self.a,[self.ci,self.bench],[rid])
        self.assertNotIn('observed_suite',r['inferred_view']['derived'])
        self.assertEqual(len(r['observed_receipts']),2)
        with self.assertRaises(ValueError):p.build(self.a,[self.ci],['absent'])
    def test_bad_measurements(self):
        for samples in [[],[True],[-1],[1.0],['12'],[float('nan')]]:
            d=json.loads(self.bench);d['records'][0]['samples_ns']=samples
            with self.assertRaises(ValueError):p.build(self.a,[json.dumps(d).encode()])
    def test_duplicate_keys(self):
        with self.assertRaises(ValueError):p.import_document(self.a,b'{"schema":1,"schema":2}')
    def test_duplicate_records(self):
        record={'subject':'checkout','status':'pass'}
        with self.assertRaises(ValueError):p.build(self.a,[self.raw(records=[record,record])])
    def test_authority_context_not_overridden(self):
        a=copy.deepcopy(self.a);a['model']['edges'][0]['context']={'lineage':'other'}
        with self.assertRaises(ValueError):p.build(a,[self.ci])
    def test_no_benchmark_speed_inference(self):
        a=copy.deepcopy(self.a);a['benchmarks']['checkout_latency']='checkout_pass'
        with self.assertRaises(ValueError):p.build(a,[self.bench])
    def test_sources_bound_exactly(self):
        r=p.import_document(self.a,self.ci)[0]
        self.assertEqual(r['source_sha256'],p.hashlib.sha256(self.ci).hexdigest())
        self.assertNotEqual(r['id'],p.import_document(self.a,self.ci+b' ')[0]['id'])
    def test_authority_bound(self):
        r=p.import_document(self.a,self.ci)[0]; a=copy.deepcopy(self.a);a['model']['horizon']=2
        self.assertNotEqual(r['id'],p.import_document(a,self.ci)[0]['id'])
if __name__=='__main__':unittest.main()
