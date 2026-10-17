"""Potential-implied bound (what a Lean potential proof can reach) vs exact DP."""
import sys, json, numpy as np
from fractions import Fraction as Fr
from refine import Automaton, prune, howard, exact_check
from direction_bound import Listed, bound
spec=json.load(open(sys.argv[1])); L,k,K=spec['L'],spec['k'],spec['K']
keys=[(tuple(e['dirs']),tuple(map(tuple,e['alpha']))) for e in spec['exclusions']]
A=Automaton(L,k,K); U,V,W,_=A.edges(Listed(keys))
m=prune(A.n,U,V); idx=np.nonzero(m)[0]
mu,cyc=howard(A.n,U[idx],V[idx],W[idx]); cyc=[idx[e] for e in cyc]; lam=Fr(int(W[cyc].sum()),len(cyc))
pi=exact_check(A.n,U,V,W,lam.numerator,lam.denominator); assert pi is not None
p,q=lam.numerator,lam.denominator
# walk of s steps from state u to v: q*sum(w) >= p*s + pi[v]-pi[u]  =>  sum(w) >= (p*s - range)/q
rng=int(pi.max()-pi.min())
t0=L-1; pre=t0-(k-1)   # internal vertices before the first full state, counted as >=1 each
init_min=min(sum(a) for (c,a) in A.sid)  # first k-1 counts inside the initial state
best=None
for v in range(t0+2,260):
    n=v-2; steps=n-t0
    T=8+pre+init_min+Fr(p*steps-rng,q)
    if T<=9214-35*v: best=v
print(json.dumps({'set':sys.argv[1].split('/')[-1],'exclusions':len(keys),'lambda':str(lam),'pot_range':rng,'potential_bound_edges':best-1,
 'dp_bound_edges':bound(A,U.astype(np.int64),V.astype(np.int64),W.astype(float))-1}))
