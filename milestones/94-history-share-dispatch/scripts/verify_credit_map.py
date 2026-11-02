"""Check the saved provenance map against the exact classified words and bytes."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(HERE/'data/credit-provenance.json');v=read(HERE/'data/variants.json')
assert len(d['rows'])==len(v['rows'])==55
def canon(word):
    seen=[];out=[]
    for x in word:
        if x not in seen:seen.append(x)
        out.append(seen.index(x))
    return out
geometric=capped=0
for p,row in zip(d['rows'],v['rows']):
    for key in ['share_index','model_index','edge','signature','caps','geometric_lower','lower','original_has_variants']:assert p[key]==row[key],(p['edge'],key)
    assert [w['word'] for w in p['word_proofs']]==row['variants']
    for w in p['word_proofs']:
        t=d['theorems'][w['geometry_theorem']]
        assert t['lower']==w['geometry_proved_lower']>=p['geometric_lower']
        assert not t['count_conditioned']
        if w['geometry_dispatch']=='canonical_eleven':assert t['directions']==w['word']
        else:
            assert p['edge']==58 and canon(w['word'][-9:])==t['directions']
        assert len(t['directions'])==w['theorem_word_length']
        assert [w['theorem_window_start_relative_to_edge']+t['local_centre_offset']+i for i in range(5)]==w['actual_centres_relative_to_edge']==[4,5,6,7,8]
        geometric+=1
        if w.get('capped_theorem'):
            t=d['theorems'][w['capped_theorem']]
            assert t['directions']==w['word'] and t['count_conditioned']
            assert t['lower']==w['capped_proved_lower']>=p['lower']
            expected=[[0,21] for _ in range(10)]
            for k,cap in p['caps'].items():expected[4+int(k)]=[0,cap]
            assert t['bounds']==expected
            capped+=1
        else:assert not p['caps'] and p['lower']==p['geometric_lower']
assert (geometric,capped)==(69,8)
for path,digest in d['inputs'].items():assert sha(ROOT/path)==digest,path
for collection in ['modules','reused_geometry_modules']:
    values=d[collection].values() if isinstance(d[collection],dict) else d[collection]
    for r in values:
        fields=[('source','source_sha256'),('object','object_sha256_current'),('log','log_sha256_current')]
        fields += [('historical_audit','historical_audit_sha256'),('build_record','build_record_sha256')] if collection=='modules' else [('audit','audit_sha256')]
        for key,hkey in fields:
            assert sha(ROOT/r[key])==r[hkey],r[key]
for t in d['theorems'].values():
    src=(ROOT/t['source']).read_text();assert t['statement'] in src,t['name']
    assert set(t['printed_axioms'])<={'propext','Classical.choice','Quot.sound'}
for name,r in d['current94_dispatch_evidence']['modules'].items():
    assert sha(ROOT/r['receipt'])==r['receipt_sha256'] and sha(ROOT/r['source'])==r['source_sha256']
out=dict(status='PASS_CLASSIFIED_WORD_CREDIT_MAP_AND_PINNED_BYTES',geometric_word_bounds=geometric,capped_word_bounds=capped,
         provenance_sha256=sha(HERE/'data/credit-provenance.json'),variants_sha256=sha(HERE/'data/variants.json'),script_sha256=sha(Path(__file__)),
         scope='Exact mapping, stated words/centres/caps, source statements and current byte pins. No import-compatibility or new local-credit proof claimed.')
(HERE/'data/credit-map-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],geometric,capped)
