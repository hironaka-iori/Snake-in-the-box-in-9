"""Maximum size of an induced linear forest (max degree 2, acyclic) in Q_n,
by SAT with lazy cycle cuts.  Usage: capq.py n tmin tmax.  Results: Q5 16, Q6 32
(Q3 5 and Q4 8 by exhaustive enumeration)."""
import itertools,sys,time
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
def comps(sel,n):
    seen=set();out=[]
    for v in sel:
        if v in seen: continue
        st=[v];seen.add(v);c=[v]
        while st:
            u=st.pop()
            for k in range(n):
                w=u^(1<<k)
                if w in sel and w not in seen: seen.add(w);st.append(w);c.append(w)
        out.append(c)
    return out
def feasible(n,t):
    V=1<<n; x=lambda v:v+1
    cls=[]
    for v in range(V):
        nb=[x(v^(1<<k)) for k in range(n)]
        for s in itertools.combinations(nb,3): cls.append([-x(v)]+[-a for a in s])
        for i in range(n):
            for j in range(i+1,n):
                a,b=v^(1<<i),v^(1<<j)
                if v<a and v<b and v<(a^(1<<j)): cls.append([-x(v),-x(a),-x(b),-x(a^(1<<j))])
    enc=CardEnc.atleast([x(v) for v in range(V)],bound=t,top_id=V,encoding=EncType.seqcounter)
    s=Solver(name='cadical195',bootstrap_with=cls+enc.clauses+[[x(0)]])
    while s.solve():
        m=s.get_model(); sel={v for v in range(V) if m[v]>0}
        cyc=False
        for c in comps(sel,n):
            cs=set(c)
            if all(sum((u^(1<<k)) in cs for k in range(n))==2 for u in c):
                s.add_clause([-x(u) for u in c]); cyc=True
        if not cyc: return sorted(sel)
    return None
n=int(sys.argv[1])
for t in range(int(sys.argv[2]),int(sys.argv[3])):
    t0=time.time(); r=feasible(n,t); print(n,t,r is not None,round(time.time()-t0,1),flush=True)
    if r is None: break
