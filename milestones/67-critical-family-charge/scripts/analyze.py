from pathlib import Path
from fractions import Fraction
import json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=model.np;alg,_=analyze_share.algorithms();data=json.loads((HERE/'data/family.json').read_text())
es=data['edges'];N=data['states'];U=np.array([e['u'] for e in es]);V=np.array([e['v'] for e in es]);results=[]
for mode in ['original_weight','weight']:
    W=np.array([e[mode] for e in es],dtype=np.int64);pool=np.flatnonzero(alg['prune'](N,U,V))
    active=np.unique(np.concatenate([U[pool],V[pool]]));index=np.full(N,-1);index[active]=np.arange(len(active))
    _,cy=alg['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=400)
    ci=pool[np.array(cy)];mu=Fraction(int(W[ci].sum()),len(ci));p,d=mu.numerator,mu.denominator
    pi=np.zeros(N,dtype=np.int64)
    for iteration in range(1000):
        nxt=pi.copy();np.minimum.at(nxt,V,pi[U]+d*W-p)
        if np.array_equal(nxt,pi):break
        pi=nxt
    else:raise AssertionError('No exact potential')
    assert np.all(p+pi[V]<=d*W+pi[U]);pi-=pi.min()
    assert all(V[e]==U[ci[(i+1)%len(ci)]] for i,e in enumerate(ci))
    row=dict(mode=mode,integer_mean=str(mu),normalized_mean=str(mu/120),potential=pi.tolist(),range=int(pi.max()),
        cycle=ci.tolist(),cyclic_states=len(active),cyclic_edges=len(pool),states=N,edges=len(es),
        scope='Exact restricted finite graph calculation; local geometry and graph certificate Lean replay pending.')
    results.append(row);print({k:v for k,v in row.items() if k not in ['potential','cycle']},flush=True)
(HERE/'data/analyses.json').write_text(json.dumps(results,indent=2)+'\n')
