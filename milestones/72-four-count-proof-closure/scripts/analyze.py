from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=analyze_share.np;alg,algsha=analyze_share.algorithms();start=time.monotonic();tag="proved-" if "--proved-only" in sys.argv else ""
meta=json.loads((HERE/f'data/{tag}model.json').read_text());sm=json.loads((ROOT/'milestones/59-extended-share-window/extended/data/model.json').read_text())
with np.load(HERE/f'build/{tag}graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
U,V,W=a['U'],a['V'],a['weight'].astype(np.int64);N=meta['states'];pool=np.flatnonzero(alg['prune'](N,U,V));active=np.unique(np.concatenate([U[pool],V[pool]]));index=np.full(N,-1,dtype=np.int32);index[active]=np.arange(len(active))
print('Cyclic states',len(active),'edges',len(pool),flush=True)
_,cycle=alg['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=400);ci=pool[np.array(cycle)];mu=Fraction(int(W[ci].sum()),len(ci));p,d=mu.numerator,mu.denominator
print('Candidate mean',mu,'cycle length',len(ci),flush=True)
pi=np.zeros(N,dtype=np.int64)
for it in range(1500):
 nxt=pi.copy();np.minimum.at(nxt,V,pi[U]+d*W-p)
 if np.array_equal(nxt,pi):break
 pi=nxt
else:raise AssertionError('No converged potential')
assert np.all(p+pi[V]<=d*W+pi[U]);pi-=min(pi);R=int(max(pi));raw=pi.astype('<i8').tobytes();(HERE/f'data/{tag}potential.i64.gz').write_bytes(gzip.compress(raw,mtime=0))
cy=[dict(edge=int(e),u=int(U[e]),v=int(V[e]),weight=int(W[e]),directions=sm['extensions'][int(a['direction'][e])],counts=[int(a['count_code'][e])//6**j%6+1 for j in range(5,-1,-1)],history=int(a['history'][e])) for e in ci]
bound=Fraction(1098960*d+8*p+R,p+4200*d)
out=dict(status='EXACT_FINITE_MODEL',integer_mean=str(mu),normalized_mean=str(mu/120),potential_range=R,potential_iterations=it+1,potential_sha256=hashlib.sha256(raw).hexdigest(),states=N,edges=len(U),cyclic_states=len(active),cyclic_edges=len(pool),cycle=cy,conditional_bound=str(bound),conditional_integer_bound=bound.numerator//bound.denominator,algorithm_sha256=algsha,seconds=time.monotonic()-start,scope=('Exact finite model using audited local exclusions; the complete arbitrary-snake graph interpretation remains pending.' if tag else 'Exact finite conditional model. Additional count exclusions and arbitrary-snake interpretation remain assumptions.'))
(HERE/f'data/{tag}analysis.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='cycle'},flush=True)
