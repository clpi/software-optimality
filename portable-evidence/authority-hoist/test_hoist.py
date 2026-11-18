import copy,json,unittest
from pathlib import Path
from loaders import baseline as b,hoisted as h,batch,PIPELINE
class Tests(unittest.TestCase):
    def test_change_is_only_hoist(self):
        before=(PIPELINE/'pipeline.py').read_text()
        expected=before.replace('    seen = set(); receipts = []','    authority_sha256 = digest(authority)  # invariant within this immutable-authority call\n    seen = set(); receipts = []').replace("'authority_sha256':digest(authority)}","'authority_sha256':authority_sha256}")
        self.assertEqual(expected,Path(h.__file__).read_text())
    def test_full_projections_scale(self):
        for n in [0,1,2,10,100]:
            a,raw=batch(n);self.assertEqual(b.build(a,[raw,raw]),h.build(a,[raw,raw]))
    def test_all_statuses(self):
        a,raw=batch(4);d=json.loads(raw)
        for record,status in zip(d['records'],['pass','fail','skipped','error']):record['status']=status
        raw=b.canonical(d);self.assertEqual(b.build(a,[raw]),h.build(a,[raw]))
    def test_context_refusals(self):
        a,raw=batch(1)
        for k in a['context']:
            d=json.loads(raw);d['context'][k]+='other'
            for fn in [b.build,h.build]:
                with self.assertRaises(ValueError):fn(a,[b.canonical(d)])
    def test_changed_authority_invalidates_id(self):
        a,raw=batch(2);changed=copy.deepcopy(a);changed['model']['horizon']=1
        old=h.import_document(a,raw);new=h.import_document(changed,raw)
        self.assertNotEqual(old[0]['id'],new[0]['id'])
        self.assertEqual(new,b.import_document(changed,raw))
    def test_byte_provenance_and_withdrawal(self):
        a,raw=batch(3);sources=[raw,raw+b' '];ids=[r['id'] for r in b.import_document(a,raw)]
        self.assertEqual(b.build(a,sources,ids),h.build(a,sources,ids))
        self.assertEqual(len(h.build(a,sources)['observed_receipts']),6)
    def test_refusals(self):
        a,raw=batch(1)
        for bad in [b'{',b'{"schema":1,"schema":2}',raw.replace(b'"pass"',b'"bogus"')]:
            for fn in [b.build,h.build]:
                with self.assertRaises(ValueError):fn(a,[bad])
    def test_stale_digest_counterfactual(self):
        a,raw=batch(1);a2=copy.deepcopy(a);a2['model']['horizon']=7
        stale=b.import_document(a,raw);fresh=b.import_document(a2,raw)
        self.assertNotEqual(stale,fresh) # a cross-call authority cache fails this oracle
    def test_hash_work_count(self):
        a,raw=batch(10)
        for mod,expected in [(b,10),(h,1)]:
            orig=mod.digest;count=[0]
            def count_digest(x):
                if x is a:count[0]+=1
                return orig(x)
            mod.digest=count_digest
            try:mod.import_document(a,raw)
            finally:mod.digest=orig
            self.assertEqual(count[0],expected)
if __name__=='__main__':unittest.main()
