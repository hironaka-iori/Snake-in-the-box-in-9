"""Exact vertex bound of the direction automaton using every cached UNSAT window."""
import sys, json
import numpy as np
from refine import Automaton, Oracle, prune, howard, exact_check
from direction_bound import bound
from fractions import Fraction as Fr
L,k,K=map(int,sys.argv[1:4])
A=Automaton(L,k,K); O=Oracle(3)
U,V,W,_=A.edges(O); m=prune(A.n,U,V); idx=np.nonzero(m)[0]
mu,cyc=howard(A.n,U[idx],V[idx],W[idx]); cyc=[idx[e] for e in cyc]
ex=Fr(int(W[cyc].sum()),len(cyc)); pi=exact_check(A.n,U,V,W,ex.numerator,ex.denominator)
vb=bound(A,U.astype(np.int64),V.astype(np.int64),W.astype(float))
print(json.dumps({'L':L,'k':k,'K':K,'edges':int(len(idx)),'min_mean':str(ex),'pot_range':int(pi.max()-pi.min()) if pi is not None else None,'max_vertices':vb,'max_edges':vb-1}))
