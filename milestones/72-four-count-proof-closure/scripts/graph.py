"""Evaluate the new interval rules; proof status is recorded separately."""
from pathlib import Path
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest()
start=time.monotonic();P=ROOT/'milestones/70-proof-supported-share-model'
meta=read(P/'data/enriched-model.json');cases=read(HERE/'data/cases.json')
tag='proved-' if '--proved-only' in sys.argv else ''
if tag:
    audit=read(HERE/'data/proof-audit.json');cases=[c for c in cases if c['number'] in audit['completed_cases']]
with np.load(P/'build/enriched-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
def canon(w):
    seen={};return [seen.setdefault(x,len(seen)) for x in w]
keep=np.ones(len(a['U']),dtype=bool);removed_by_case={c['number']:0 for c in cases}
for di,ds in enumerate(sm['extensions']):
    ix=np.flatnonzero(a['direction']==di);codes=a['count_code'][ix]
    cs=np.stack([codes//6**j%6+1 for j in range(5,-1,-1)],axis=1)
    bad=np.zeros(len(ix),dtype=bool)
    for case in cases:
        hit=np.zeros(len(ix),dtype=bool)
        for offset in range(2,5):
            for reverse in [False,True]:
                piece=ds[offset:offset+5]
                if canon(piece[::-1] if reverse else piece)!=case['dirs']:continue
                indices=[offset+(5-j if reverse else j)-3 for j in range(1,5)]
                test=np.ones(len(ix),dtype=bool)
                for j,(lo,hi) in zip(indices,case['bounds']):
                    assert hi<6 or hi==21
                    test&=(cs[:,j]>=lo)&(cs[:,j]<=hi)
                hit|=test
        removed_by_case[case['number']]+=int(hit.sum());bad|=hit
    keep[ix]=~bad
out={k:v[keep] for k,v in a.items()};np.savez_compressed(HERE/f'build/{tag}graph.npz',**out)
report=dict(states=meta['states'],edges=int(keep.sum()),candidate_edges=len(keep),removed=int((~keep).sum()),removed_by_case=removed_by_case,arrays_sha256={k:sha(v.tobytes()) for k,v in out.items()},source_arrays_sha256=meta['arrays_sha256'],seconds=time.monotonic()-start,scope='Finite comparison under the new interval exclusions. Consult the Lean audit for completed proofs; no global bound follows from this graph alone.')
report['applied_cases']=[c['number'] for c in cases]
(HERE/f'data/{tag}model.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)
