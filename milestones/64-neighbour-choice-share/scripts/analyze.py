from pathlib import Path
from fractions import Fraction
import json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=model.np;alg,_=analyze_share.algorithms()
old=json.loads((ROOT/'milestones/63-long-window-splits/data/analysis.json').read_text())
rows=json.loads((HERE/'data/choices.json').read_text())['rows'];edges=[]
for e,r in zip(old['edges'],rows):
    assert e['directions']==r['directions']
    edges.append(dict(e,old_weight=e['weight'],weight=120*e['counts'][-1]+max(r['old'],r['lower'])))
N=old['states'];u=np.array([e['u'] for e in edges]);v=np.array([e['v'] for e in edges]);w=np.array([e['weight'] for e in edges],dtype=np.int64)
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
out=dict(length=11,states=N,edges=edges,integer_mean=str(mu),normalized_mean=str(mu/120),potential=pi.tolist(),range=int(pi.max()),cycle=chosen.tolist(),
    scope='Exact restricted graph minimum; local theorem status is recorded separately in lean-audit.json. No global bound.')
(HERE/'data/analysis.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['edges','potential','cycle']},flush=True)
