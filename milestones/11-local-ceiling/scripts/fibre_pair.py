"""Find vertex-disjoint A, B in Q_a, each inducing a union of cycles of length >= G, max |A|+|B|."""
import sys, time, itertools, json
from ortools.sat.python import cp_model
a=int(sys.argv[1]); G=int(sys.argv[2]); tl=float(sys.argv[3]); N=1<<a
def comps(S):
    seen=set(); out=[]
    for s in S:
        if s in seen: continue
        st=[s]; c=[]
        while st:
            v=st.pop()
            if v in seen: continue
            seen.add(v); c.append(v); st+=[v^1<<k for k in range(a) if v^1<<k in S]
        out.append(c)
    return out
cuts=[]; t0=time.time(); best=None
while time.time()-t0<tl:
    m=cp_model.CpModel()
    X=[[m.NewBoolVar("") for v in range(N)] for _ in range(2)]
    for v in range(N):
        m.AddBoolOr([X[0][v].Not(), X[1][v].Not()])
        for t in range(2):
            m.Add(sum(X[t][v^1<<k] for k in range(a))==2).OnlyEnforceIf(X[t][v])
            for p,q in itertools.combinations(range(a),2):
                if v>>p&1 or v>>q&1: continue
                m.AddBoolOr([X[t][w].Not() for w in (v,v|1<<p,v|1<<q,v|1<<p|1<<q)])
    for t,c in cuts: m.AddBoolOr([X[t][v].Not() for v in c])
    m.AddBoolOr([X[0][0]])
    m.Maximize(sum(X[0])+sum(X[1]))
    s=cp_model.CpSolver(); s.parameters.num_workers=8; s.parameters.max_time_in_seconds=max(5,tl-(time.time()-t0))
    r=s.Solve(m)
    sets=[{v for v in range(N) if s.Value(X[t][v])} for t in range(2)]
    bad=[(t,c) for t in range(2) for c in comps(sets[t]) if len(c)<G]
    if not bad:
        res={'a':a,'G':G,'total':len(sets[0])+len(sets[1]),'status':'OPT' if r==cp_model.OPTIMAL else 'FEAS',
             'A':sorted(sets[0]),'B':sorted(sets[1]),
             'cyclesA':sorted(len(c) for c in comps(sets[0])),'cyclesB':sorted(len(c) for c in comps(sets[1]))}
        print(json.dumps({k:v for k,v in res.items() if k not in 'AB'}), flush=True)
        json.dump(res, open(f'fibre_a{a}_G{G}.json','w')); break
    cuts+=bad
else: print('timeout', a, G, len(cuts))
