"""Combine exhaustive crossing and first-edge divisions of the open43 cases."""
from pathlib import Path
import json,hashlib,collections
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
base=R/'milestones/225-replacement-widths/data/pair43.json';rows=read(base)['results'];raw=read(H/'data/regions43.json')
open_ids={r['id'] for r in rows if r['status']=='UNKNOWN'};ordinary=open_ids-{114};assert len(ordinary)==24
pins={str(base):sha(base),str(H/'data/regions43.json'):sha(H/'data/regions43.json')}
for tag,crossing in [('split43-zero',0),('split43-two',2)]:
    p=H/'data'/(tag+'.json');e=p.with_name(tag+'-execution.json');j=read(p);receipt=read(e)
    assert receipt['status']=='ACCEPTED_NATIVE_RESULT' and sha(p)==receipt['result_sha256']
    assert all(sha(q)==v for q,v in receipt['pins'].items())
    assert j['arguments']['first_crossings']==crossing and j['arguments']['width']==43
    assert len(j['results'])==24 and {r['id'] for r in j['results']}==ordinary
    assert all(r['status']=='INFEASIBLE' for r in j['results'])
    pins[str(p)]=sha(p);pins[str(e)]=sha(e)
for i in ordinary:
    row=raw['contexts'][i];assert row['replacement_crossings']==2
    assert all((p['anchors'][0]^p['anchors'][1])&256==0 for p in row['parts'])
row=raw['contexts'][114];assert row['replacement_crossings']==1
assert [((p['anchors'][0]^p['anchors'][1])>>8)&1 for p in row['parts']]==[0,1]
anchor=row['parts'][0]['anchors'][0]
children=sorted(v for v in row['parts'][0]['allowed'] if (v^anchor).bit_count()==1 and v^anchor!=256)
assert children==[19,49]
for neighbour in children:
    tag=f'first114-{neighbour}';p=H/'data'/(tag+'.json');e=p.with_name(tag+'-execution.json');j=read(p);receipt=read(e)
    assert receipt['status']=='ACCEPTED_NATIVE_RESULT' and sha(p)==receipt['result_sha256']
    assert all(sha(q)==v for q,v in receipt['pins'].items())
    assert j['arguments']['first_neighbour']==neighbour and j['arguments']['first_crossings']==0
    assert len(j['results'])==1 and j['results'][0]['id']==114 and j['results'][0]['status']=='INFEASIBLE'
    pins[str(p)]=sha(p);pins[str(e)]=sha(e)
final=[dict(r,combined_status='COVER_EXCLUDED' if r['id'] in open_ids else r['status']) for r in rows]
assert len(final)==294 and len({r['id'] for r in final})==294
assert all(r['combined_status'] in ['INHERITED_EXCLUDED','INFEASIBLE','STATIC_EXCLUDED','COVER_EXCLUDED'] for r in final)
out=dict(status='COMPLETE_NATIVE_EXCLUSION',contexts=final,counts=dict(collections.Counter(r['combined_status'] for r in final)),pins=pins,scope='The specified seed and endpoint24 target, four total crossings, two length-preserving replacement blocks of at most43edges. Generic parity and path facts are Lean-checked; concrete domain/coverage/model validity and solver contradictions remain native or independently audited. No global bound.')
(H/'data/coverage43.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],out['counts'])
