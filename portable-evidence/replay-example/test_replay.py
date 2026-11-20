import copy, itertools, json, unittest
from pathlib import Path
import replay
p=replay.pipeline
FIX=Path(p.__file__).parent/'fixtures'
class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.a=json.loads((FIX/'authority.json').read_text()); self.c=(FIX/'ci.json').read_bytes(); self.b=(FIX/'benchmark.json').read_bytes()
    def test_all_short_delivery_words(self):
        for n in range(5):
            for sources in itertools.product([self.c,self.b,self.c+b' '],repeat=n):
                self.assertEqual(p.build(self.a,sources),replay.build(self.a,sources))
    def test_retains_byte_distinct_provenance(self):
        self.assertEqual(len(replay.build(self.a,[self.c,self.c+b' '])['observed_receipts']),2)
    def test_conflict_retained(self):
        d=json.loads(self.c); d['records'][0]['status']='fail'
        r=replay.build(self.a,[self.c,json.dumps(d).encode(),self.c])
        self.assertEqual(r['inferred_view']['capabilities']['checkout-case'],'conflict')
    def test_withdrawal(self):
        rid=p.import_document(self.a,self.c)[0]['id']; sources=[self.c,self.b,self.c]*5
        self.assertEqual(p.build(self.a,sources,[rid]),replay.build(self.a,sources,[rid]))
    def test_unknown_withdrawal_fails(self):
        with self.assertRaises(ValueError):replay.build(self.a,[self.c],['unknown'])
    def test_invalid_not_hidden(self):
        for raw in [b'{',b'{"schema":1,"schema":2}',self.c.replace(b'"pass"',b'"bad"')]:
            with self.assertRaises(ValueError):replay.build(self.a,[self.c,raw,raw])
    def test_no_cross_authority_cache(self):
        replay.build(self.a,[self.c]);a=copy.deepcopy(self.a);a['context']['lineage']='other'
        with self.assertRaises(ValueError):replay.build(a,[self.c])
    def test_reject_mutable_input(self):
        with self.assertRaises(ValueError):replay.build(self.a,[bytearray(self.c)])
    def test_bad_subject_cache_control(self):
        # The tempting subject-only cache drops the failing receipt; this oracle catches it.
        d=json.loads(self.c);d['records'][0]['status']='fail'; bad=json.dumps(d).encode()
        self.assertNotEqual(p.build(self.a,[self.c,bad]),p.build(self.a,[self.c]))
if __name__=='__main__':unittest.main()
