# Maximum induced linear forest (max degree <= 2, acyclic) in Q5, via CP-SAT + lazy cycle cuts.
from ortools.sat.python import cp_model
N = 5; V = 1 << N
def comps(sel):
    seen=set(); out=[]
    for s in sel:
        if s in seen: continue
        st=[s]; c=[]
        while st:
            u=st.pop()
            if u in seen: continue
            seen.add(u); c.append(u); st += [u ^ (1<<k) for k in range(N) if (u ^ (1<<k)) in sel]
        out.append(c)
    return out
for maxcomp in [1, 2, 3, 4, 99]:
    M = cp_model.CpModel(); x = [M.new_bool_var('') for _ in range(V)]
    for v in range(V):
        M.add(sum(x[v ^ (1<<k)] for k in range(N)) <= 2).only_enforce_if(x[v])
    if maxcomp < 99:
        # components = vertices - edges for a forest
        e = []
        for v in range(V):
            for k in range(N):
                w = v ^ (1<<k)
                if v < w:
                    b = M.new_bool_var(''); M.add_multiplication_equality(b, [x[v], x[w]]); e.append(b)
        M.add(sum(x) - sum(e) <= maxcomp)
    M.maximize(sum(x))
    while True:
        s = cp_model.CpSolver(); s.parameters.num_workers = 4; s.parameters.max_time_in_seconds = 120
        r = s.solve(M); sel = {v for v in range(V) if s.value(x[v])}
        cyc = [c for c in comps(sel) if all(sum((u ^ (1<<k)) in sel for k in range(N)) == 2 for u in c)]
        if not cyc: break
        for c in cyc: M.add(sum(x[u] for u in c) <= len(c) - 1)
    print('Q5 max induced linear forest with <=', maxcomp, 'components:', len(sel), s.status_name(r))
