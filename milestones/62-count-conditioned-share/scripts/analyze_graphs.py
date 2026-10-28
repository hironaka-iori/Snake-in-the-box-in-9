"""Measure certified geometric credits on the existing restricted families."""
from pathlib import Path
from fractions import Fraction
import json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=model.np;alg,_=analyze_share.algorithms()
def canon(ds):
    names={};return tuple(names.setdefault(x,len(names)) for x in ds)
rows=json.loads((HERE/'data/split-share.json').read_text())['rows']
credits={tuple(r['directions']):r['lower'] for r in rows if r['lower']>r['old']}
results=[]
for n in [9,10,11]:
    prior=ROOT/'milestones/61-critical-family-share/data'
    es=json.loads((prior/'critical-edges.json').read_text()) if n==9 else json.loads((prior/f'lift-{n}.json').read_text())['edges']
    nodes=sorted({e['u'] for e in es}|{e['v'] for e in es});idx={v:i for i,v in enumerate(nodes)}
    edges=[]
    for e in es:
        lower=credits.get(canon(e['directions'][-9:]),0)
        edges.append(dict(u=idx[e['u']],v=idx[e['v']],weight=120*e['counts'][-1]+max(e['share_lower'],lower),
            old_weight=e['weight'],split_lower=lower,directions=e['directions'],counts=e['counts']))
    N=len(nodes);u=np.array([e['u'] for e in edges]);v=np.array([e['v'] for e in edges]);w=np.array([e['weight'] for e in edges],dtype=np.int64)
    pool=np.flatnonzero(alg['prune'](N,u,v));active=np.unique(np.concatenate([u[pool],v[pool]]));index=np.full(N,-1);index[active]=np.arange(len(active))
    _,c=alg['howard'](len(active),index[u[pool]],index[v[pool]],w[pool],iters=400)
    chosen=pool[np.array(c)];mu=Fraction(int(w[chosen].sum()),len(chosen));p,q=mu.numerator,mu.denominator
    pi=np.zeros(N,dtype=np.int64)
    for iteration in range(500):
        nxt=pi.copy();np.minimum.at(nxt,v,pi[u]+q*w-p)
        if np.array_equal(nxt,pi):break
        pi=nxt
    else:raise AssertionError('No potential')
    assert np.all(p+pi[v]<=q*w+pi[u]);pi-=pi.min()
    assert all(v[i]==u[chosen[(j+1)%len(chosen)]] for j,i in enumerate(chosen))
    result=dict(length=n,states=N,edges=edges,improved_edges=sum(e['weight']>e['old_weight'] for e in edges),
        integer_mean=str(mu),normalized_mean=str(mu/120),potential=pi.tolist(),range=int(pi.max()),cycle=chosen.tolist(),
        scope='Restricted critical family only. All-edge integer potential and attaining cycle; no global bound.')
    results.append(result);print({k:v for k,v in result.items() if k not in ['edges','potential','cycle']},flush=True)
(HERE/'data/graph-analyses.json').write_text(json.dumps(results,indent=2)+'\n')
