"""Lower bounds for g_8(c) by fibre constructions: Q8 = Q_m x Q_(8-m); fibres over
even-weight y carry A, odd-weight y carry B, with A, B vertex-disjoint induced
linear forests of Q_m.  Result: 2^(7-m)(|A|+|B|) vertices, 2^(7-m)(cA+cB) paths.
SAT search for disjoint A (<= cA paths) and B (<= cB paths) with |A|+|B| >= L.
usage: python3 fibre_forest.py m cA cB L [timeout]"""
import sys, time
from itertools import combinations
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from forest_pack import cycles
def forest(m, pool, cl, tag, c):
    V=1<<m; s=[pool.id((tag,u)) for u in range(V)]; ends=[]
    for u in range(V):
        nb=[s[u^(1<<i)] for i in range(m)]
        for x in CardEnc.atmost(nb,bound=2,vpool=pool,encoding=EncType.seqcounter).clauses: cl.append(x+[-s[u]])
        e1=pool.id((tag,'e1',u)); e0=pool.id((tag,'e0',u)); pr=[]
        for a,b in combinations(range(m),2):
            p=pool.id((tag,'p',u,a,b)); pr.append(p); cl.append([-p,nb[a]]); cl.append([-p,nb[b]])
        cl.append([-s[u],e1]+pr); cl.append([-s[u],e0]+nb); ends+=[e1,e0]
    for x in CardEnc.atmost(ends,bound=2*c,vpool=pool,encoding=EncType.seqcounter).clauses: cl.append(x)
    return s
def run(m,cA,cB,L,tmax):
    pool=IDPool(); cl=[]
    A=forest(m,pool,cl,'A',cA); B=forest(m,pool,cl,'B',cB)
    for u in range(1<<m): cl.append([-A[u],-B[u]])
    for x in CardEnc.atleast(A+B,bound=L,vpool=pool,encoding=EncType.seqcounter).clauses: cl.append(x)
    cl.append([A[0]])
    t0=time.time()
    with Solver(name='cadical153',bootstrap_with=cl) as sol:
        while time.time()-t0<tmax:
            if not sol.solve(): return 'UNSAT',None
            md=sol.get_model()
            a={u for u in range(1<<m) if md[A[u]-1]>0}; b={u for u in range(1<<m) if md[B[u]-1]>0}
            ca,cb=cycles(a,m),cycles(b,m)
            if not ca and not cb: return 'SAT',(sorted(a),sorted(b))
            for cy in ca: sol.add_clause([-A[u] for u in cy])
            for cy in cb: sol.add_clause([-B[u] for u in cy])
    return 'UNKNOWN',None
if __name__=='__main__':
    m,cA,cB,L=map(int,sys.argv[1:5]); tmax=float(sys.argv[5]) if len(sys.argv)>5 else 120
    st,w=run(m,cA,cB,L,tmax); f=2**(7-m)
    print('m=%d cA=%d cB=%d |A|+|B|>=%d: %s  -> g8(%d) >= %s'%(m,cA,cB,L,st,f*(cA+cB),f*L if st=='SAT' else '?'),flush=True)
    if w: print(' A',w[0],'\n B',w[1])
