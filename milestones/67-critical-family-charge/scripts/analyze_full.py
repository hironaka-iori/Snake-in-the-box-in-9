from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
name=sys.argv[1] if len(sys.argv)>1 else 'full'
assert name in ['full']
np=model.np;start=time.monotonic();meta=json.loads((HERE/f'data/{name}-model.json').read_text())
with np.load(HERE/f'build/{name}-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
U,V,W=a['U'],a['V'],a['weight'].astype(np.int64);N=meta['states'];alg,sha=analyze_share.algorithms()
pool=np.flatnonzero(alg['prune'](N,U,V));active=np.unique(np.concatenate([U[pool],V[pool]]))
index=np.full(N,-1,dtype=np.int32);index[active]=np.arange(len(active))
print('Cyclic states',len(active),'edges',len(pool),flush=True)
_,cy=alg['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=400)
chosen=pool[np.array(cy)];mu=Fraction(int(W[chosen].sum()),len(chosen));p,d=mu.numerator,mu.denominator
assert all(V[e]==U[chosen[(i+1)%len(chosen)]] for i,e in enumerate(chosen))
print('Candidate integer mean',mu,'normalized',mu/120,'period',len(chosen),flush=True)
pi=np.zeros(N,dtype=np.int64)
for iteration in range(1500):
    nxt=pi.copy();np.minimum.at(nxt,V,pi[U]+d*W-p)
    if np.array_equal(nxt,pi):break
    pi=nxt
    if iteration%50==0:print('Potential iteration',iteration,flush=True)
else:raise AssertionError('No exact potential found')
assert np.all(p+pi[V]<=d*W+pi[U]);pi-=pi.min();R=int(pi.max())
raw=pi.astype('<i8').tobytes();(HERE/f'data/{name}-potential.i64.gz').write_bytes(gzip.compress(raw,mtime=0))
source=ROOT/'milestones/59-extended-share-window/extended';source_meta=json.loads((source/'data/model.json').read_text())
with np.load(source/'build/graph.npz') as z:sa={k:z[k] for k in ['direction','count_code','share_lower']}
cycle=[]
for e in chosen:
    s=int(a['source_edge'][e]);cycle.append(dict(edge=int(e),u=int(U[e]),v=int(V[e]),weight=int(W[e]),
        history=int(a['history'][e]),directions=source_meta['extensions'][int(sa['direction'][s])],
        counts=analyze_share.decode(int(sa['count_code'][s]),6),share_lower=int(sa['share_lower'][s])))
bound=Fraction(1099680*d+8*p+R,p+4200*d)
out=dict(status='EXACT_FINITE_MODEL',integer_mean=str(mu),normalized_mean=str(mu/120),
    source_mean='9891/20',mean_increase=str(mu-Fraction(9891,20)),potential_range=R,potential_iterations=iteration+1,
    potential_sha256=hashlib.sha256(raw).hexdigest(),states=N,edges=len(U),cyclic_states=len(active),cyclic_edges=len(pool),
    cycle=cycle,conditional_bound=str(bound),conditional_integer_bound=bound.numerator//bound.denominator,
    algorithm_source_sha256=sha,seconds=time.monotonic()-start,
    scope='Exact finite graph computation only. Imported numerical premises, history recognition and complete arbitrary-snake assembly remain separate proof obligations.')
(HERE/f'data/{name}-analysis.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='cycle'},flush=True)
