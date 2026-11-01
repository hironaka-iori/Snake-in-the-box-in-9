"""Independently reconstruct every weight, potential inequality, and cycle sum."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
tag=sys.argv[1]
meta=read(HERE/f'data/{tag}-model.json');res=read(HERE/f'data/{tag}-analysis.json')
source=read(HERE/'data/source-proved-model.json')
with np.load(HERE/'build/source-graph.npz') as z:base={k:z[k] for k in z.files}
with np.load(HERE/f'build/{tag}-graph.npz') as z:a={k:z[k] for k in z.files}
for k,v in a.items():
 assert sha(v.tobytes())==meta['arrays_sha256'][k]
 assert sha(base[k].tobytes())==source['arrays_sha256'][k]
 if k!='weight':assert np.array_equal(v,base[k])
def canon(w):
 out=[];seen=[]
 for x in w:
  if x not in seen:seen.append(x)
  out.append(seen.index(x))
 return tuple(out)
shape_set={tuple(s) for s in meta['countfree_shapes']};words=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
lower=np.zeros(len(words),dtype=np.int64)
for i,w in enumerate(words):
 q=w[-6:]
 if canon(q) in shape_set or canon(q[::-1]) in shape_set:
  key=''.join(map(str,min(canon(q),canon(q[::-1]))))
  lower[i]=meta.get('countfree_overrides',{}).get(key,meta['countfree_share_lower'])
expected=np.maximum(base['weight'],120*(a['count_code']%6+1)+lower[a['direction']])
assert np.array_equal(a['weight'],expected)
raw=gzip.decompress((HERE/f'data/{tag}-potential.i64.gz').read_bytes());assert sha(raw)==res['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');mu=Fraction(res['integer_mean']);p,d=mu.numerator,mu.denominator
assert len(pi)==meta['states'] and min(pi)==0 and max(pi)==res['potential_range']
slack=d*a['weight']+pi[a['U']]-pi[a['V']]-p;assert min(slack)>=0
cycle=res['cycle'];total=0
for i,c in enumerate(cycle):
 e=c['edge'];nxt=cycle[(i+1)%len(cycle)]
 assert c['u']==int(a['U'][e]) and c['v']==int(a['V'][e])==nxt['u']
 assert c['weight']==int(a['weight'][e]);assert slack[e]==0
 assert c['directions']==words[int(a['direction'][e])]
 total+=c['weight']
assert Fraction(total,len(cycle))==mu
bound=Fraction(1098960*d+8*p+res['potential_range'],p+4200*d)
assert str(bound)==res['conditional_bound'] and bound.numerator//bound.denominator==res['conditional_integer_bound']
out=dict(status='PASS_EXACT_CONDITIONAL_MODEL',source_arrays_sha256=source['arrays_sha256'],arrays_sha256=meta['arrays_sha256'],potential_sha256=sha(raw),all_weights_reconstructed=True,edge_inequalities=len(slack),minimum_slack=int(min(slack)),attaining_cycle_edges=len(cycle),mean=str(mu),potential_range=int(max(pi)),conditional_bound=str(bound),conditional_integer_bound=bound.numerator//bound.denominator,scope=meta['scope'])
(HERE/f'data/{tag}-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if 'sha256' not in k})
