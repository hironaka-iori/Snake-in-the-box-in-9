"""Separate the effects of unproved share gains and validity exclusions."""
from pathlib import Path
from fractions import Fraction
import json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=model.np;alg,_=analyze_share.algorithms()
old=json.loads((ROOT/'milestones/64-neighbour-choice-share/data/analysis.json').read_text())
rows=json.loads((HERE/'data/summary.json').read_text())['results'];out=[]
for mode in ['shares_only','exclusions_only','combined']:
    es=[]
    for i,(e,r) in enumerate(zip(old['edges'],rows)):
        if mode!='shares_only' and r['lower'] is None:continue
        weight=e['weight']
        if mode!='exclusions_only' and r['lower'] is not None:weight=120*e['counts'][-1]+r['lower']
        es.append(dict(e,source_edge=i,weight=weight))
    N=old['states'];u=np.array([e['u'] for e in es]);v=np.array([e['v'] for e in es]);w=np.array([e['weight'] for e in es],dtype=np.int64)
    pool=np.flatnonzero(alg['prune'](N,u,v));result=dict(mode=mode,edges=es,states=N,cyclic_edges=len(pool))
    if len(pool):
        active=np.unique(np.concatenate([u[pool],v[pool]]));index=np.full(N,-1);index[active]=np.arange(len(active))
        _,c=alg['howard'](len(active),index[u[pool]],index[v[pool]],w[pool],iters=400)
        chosen=pool[np.array(c)];mu=Fraction(int(w[chosen].sum()),len(chosen));p,q=mu.numerator,mu.denominator
        pi=np.zeros(N,dtype=np.int64)
        for it in range(500):
            nxt=pi.copy();np.minimum.at(nxt,v,pi[u]+q*w-p)
            if np.array_equal(nxt,pi):break
            pi=nxt
        else:raise AssertionError('Potential did not converge')
        assert np.all(p+pi[v]<=q*w+pi[u]);pi-=pi.min()
        assert all(v[i]==u[chosen[(j+1)%len(chosen)]] for j,i in enumerate(chosen))
        result.update(integer_mean=str(mu),normalized_mean=str(mu/120),potential=pi.tolist(),cycle=chosen.tolist())
    result['scope']='Conditional diagnostic only: count-conditioned local bounds and exclusions have not passed Lean replay. No certified graph or global bound.'
    out.append(result);print({k:v for k,v in result.items() if k not in ['edges','potential','cycle']},flush=True)
(HERE/'data/candidate-analyses.json').write_text(json.dumps(out,indent=2)+'\n')
