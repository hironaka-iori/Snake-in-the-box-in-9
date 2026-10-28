from pathlib import Path
from fractions import Fraction
import json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=model.np;alg,_=analyze_share.algorithms()
results=[]
for n in [10,11]:
    data=json.loads((HERE/f'data/lift-{n}.json').read_text());edges=data['edges'];N=data['states']
    u=np.array([e['u'] for e in edges]);v=np.array([e['v'] for e in edges]);pool=np.flatnonzero(alg['prune'](N,u,v))
    active=np.unique(np.concatenate([u[pool],v[pool]]));index=np.full(N,-1);index[active]=np.arange(len(active))
    for kind in ['base','share']:
        weight=np.array([120*e['counts'][-1]+e['base_share'] if kind=='base' else e['weight'] for e in edges],dtype=np.int64)
        _,c=alg['howard'](len(active),index[u[pool]],index[v[pool]],weight[pool],iters=400)
        chosen=pool[np.array(c)];mu=Fraction(int(weight[chosen].sum()),len(chosen));p,q=mu.numerator,mu.denominator
        pi=np.zeros(N,dtype=np.int64)
        for iteration in range(500):
            nxt=pi.copy();np.minimum.at(nxt,v,pi[u]+q*weight-p)
            if np.array_equal(nxt,pi):break
            pi=nxt
        else:raise AssertionError('No all-edge potential')
        assert np.all(p+pi[v]<=q*weight+pi[u]);pi-=pi.min()
        assert all(v[i]==u[chosen[(j+1)%len(chosen)]] for j,i in enumerate(chosen))
        result=dict(length=n,mode=kind,states=N,edges=len(edges),cyclic_states=len(active),cyclic_edges=len(pool),
                    integer_mean=str(mu),normalized_mean=str(mu/120),potential=pi.tolist(),range=int(pi.max()),cycle=chosen.tolist(),
                    scope='Exact minimum of the restricted lifted critical graph only; no global bound.')
        results.append(result);print({k:v for k,v in result.items() if k not in ['potential','cycle']},flush=True)
(HERE/'data/analyses.json').write_text(json.dumps(results,indent=2)+'\n')
