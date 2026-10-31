"""Evaluate the share-120 premise without claiming its geometric proof."""
from pathlib import Path
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];P=HERE.parent
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
meta=read(P/'data/proved-model.json');result=read(P/'data/proved-analysis.json')
with np.load(P/'build/proved-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
raw=gzip.decompress((P/'data/proved-potential.i64.gz').read_bytes());assert sha(raw)==result['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');assert result['integer_mean']=='480'
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json');hit=np.zeros(len(a['U']),dtype=bool)
for di,ds in enumerate(sm['extensions']):
    if len(set(ds[-6:]))!=6:continue
    ids=np.flatnonzero(a['direction']==di);c=a['count_code'][ids]
    cs=np.stack([c//6**j%6+1 for j in range(4,-1,-1)],axis=1)
    hit[ids]=np.all(cs==np.array([4,5,4,2,6]),axis=1)|np.all(cs==np.array([6,2,4,5,4]),axis=1)
base=120*(a['count_code']%6+1);weights=a['weight'].copy();weights[hit]=np.maximum(weights[hit],base[hit]+120)
assert np.all(480+pi[a['V']]<=weights+pi[a['U']])
cycle=result['cycle'];assert all(not hit[c['edge']] for c in cycle)
assert all(c['v']==cycle[(i+1)%len(cycle)]['u'] for i,c in enumerate(cycle))
assert sum(int(weights[c['edge']]) for c in cycle)==480*len(cycle)
out=dict(status='PASS_CONDITIONAL_MODEL_EFFECT',assumed_share_lower=120,matching_edges=int(hit.sum()),improved_edges=int((weights>a['weight']).sum()),minimum_mean_before='480',minimum_mean_after='480',attaining_cycle_unchanged=True,source_cases=meta['applied_cases'],source_arrays_sha256=meta['arrays_sha256'],scope='Exact finite-model result conditional on the proposed share inequality. Its addition alone cannot improve the mean; other surviving cycles remain.')
(HERE/'data/candidate-effect.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
