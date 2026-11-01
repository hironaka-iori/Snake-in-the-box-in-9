"""Pin the ten-case graph and apply only the checked same-centre share bound."""
from pathlib import Path
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];P=HERE.parent;ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
audit=read(P/'critical-charge/share-proof/data/proof-audit.json');assert audit['status']=='PASS_LOCAL_SHARE_THEOREM'
meta=read(P/'data/proved-model.json');result=read(P/'data/proved-analysis.json')
with np.load(P/'build/proved-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
original=meta['arrays_sha256'].copy();sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json');changed=np.zeros(len(a['U']),dtype=bool)
for di,ds in enumerate(sm['extensions']):
 if len(set(ds[-6:]))!=6:continue
 ix=np.flatnonzero(a['direction']==di);codes=a['count_code'][ix];cs=np.stack([codes//6**j%6+1 for j in range(4,-1,-1)],axis=1)
 hit=np.all(cs==[4,5,4,2,6],axis=1)|np.all(cs==[6,2,4,5,4],axis=1);ix=ix[hit]
 raised=np.maximum(a['weight'][ix],120*(a['count_code'][ix]%6+1)+120);changed[ix]=raised>a['weight'][ix];a['weight'][ix]=raised
raw=gzip.decompress((P/'data/proved-potential.i64.gz').read_bytes());assert sha(raw)==result['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8')
assert np.all(480+pi[a['V']]<=a['weight']+pi[a['U']])
for c in result['cycle']:assert not changed[c['edge']] and int(a['weight'][c['edge']])==c['weight']
meta.update(source_arrays_sha256=original,arrays_sha256={k:sha(v.tobytes()) for k,v in a.items()},share_lower=120,improved_edges=int(changed.sum()),share_audit_sha256=sha((P/'critical-charge/share-proof/data/proof-audit.json').read_bytes()),scope='Ten audited count cases and checked local share-120 rule, including reversal. Full arbitrary-snake graph interpretation remains pending.')
np.savez_compressed(HERE/'build/source-graph.npz',**a)
(HERE/'data/source-proved-model.json').write_text(json.dumps(meta,indent=2)+'\n')
(HERE/'data/source-proved-analysis.json').write_text(json.dumps(result,indent=2)+'\n')
(HERE/'data/source-potential.i64.gz').write_bytes(gzip.compress(raw,mtime=0))
print('Edges',len(a['U']),'improved',int(changed.sum()),'exact mean 480 retained',flush=True)
