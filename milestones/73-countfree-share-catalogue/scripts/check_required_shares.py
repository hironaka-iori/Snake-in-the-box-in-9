"""Exact necessary shape floors for the saved 496/range-600 potential only."""
from pathlib import Path
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/72-four-count-proof-closure/critical-current'
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
source=read(OLD/'data/source-proved-model.json')
with np.load(OLD/'build/source-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in source['arrays_sha256'].items():assert sha(a[k].tobytes())==h
tag='countfree16-all-except012034x20-except012310x12'
meta=read(OLD/f'data/{tag}-analysis.json')
raw=gzip.decompress((OLD/f'data/{tag}-potential.i64.gz').read_bytes())
assert sha(raw)==meta['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8')
assert min(pi)==0 and max(pi)==600
need=496+pi[a['V']]-pi[a['U']]
missing=need>a['weight'];entering=a['count_code'].astype(np.int64)%6+1
extensions=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
def canon(word):
    d={};return tuple(d.setdefault(x,len(d)) for x in word)
def shape(word):return min(canon(word),canon(word[::-1]))
portfolio=read(OLD/'data/portfolio.json')['selected'];rows=[];covered=np.zeros(len(need),dtype=bool)
weights=a['weight'].astype(np.int64).copy()
for index,case in enumerate(portfolio):
    sh=tuple(case['directions']);direction_ids=[i for i,d in enumerate(extensions) if shape(d[-6:])==sh]
    ix=missing & np.isin(a['direction'],direction_ids)
    edges=np.flatnonzero(ix);covered |= ix
    required=int(np.max((need-120*entering)[edges])) if len(edges) else 0
    assert required<=case['required_share']
    witness=None
    if len(edges):
        e=int(edges[np.argmax((need-120*entering)[edges])]);witness=dict(edge=e,u=int(a['U'][e]),v=int(a['V'][e]),base_weight=int(a['weight'][e]),required_edge_weight=int(need[e]),entering_count=int(entering[e]))
    all_ix=np.isin(a['direction'],direction_ids)
    weights[all_ix]=np.maximum(weights[all_ix],120*entering[all_ix]+required)
    rows.append(dict(case_number=7300+index,shape=list(sh),selected_share=case['required_share'],least_share_for_fixed_potential=required,dependent_edges=len(edges),necessity_witness=witness))
assert np.array_equal(covered,missing)
assert np.all(496+pi[a['V']]<=weights+pi[a['U']])
out=dict(status='EXACT_FIXED_POTENTIAL_REQUIREMENTS',edges=len(need),dependent_edges=int(missing.sum()),
    mean=496,potential_range=600,potential_sha256=sha(raw),requirements=rows,
    source_arrays_sha256=source['arrays_sha256'],
    scope='Coordinatewise least nonnegative shape floors for this fixed graph and potential, allowing no other new rules. A witness establishes necessity for each positive floor. Alternative potentials and graph restrictions are not excluded. These are proof obligations, not new geometric share theorems.')
(HERE/'data').mkdir(exist_ok=True);(HERE/'data/required-shares.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],[(r['case_number'],r['least_share_for_fixed_potential'],r['dependent_edges']) for r in rows],flush=True)
