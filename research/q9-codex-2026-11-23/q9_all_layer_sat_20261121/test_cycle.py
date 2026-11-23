from layers import *
record = next(json.loads(s) for s in (BASE/'controls0.jsonl').read_text().splitlines() if json.loads(s)['status']=='SAT')
p=record['path']
s=next(i-1 for i,x in enumerate(p) if x//32!=p[0]//32)
t=next(i for i,x in enumerate(p) if x//32==p[-1]//32)
p=p[s:t+1]
verify(p,record['word'])
a=set(p)
avoid=a|{v^(1<<d) for v in a for d in range(9)}
cycle=next([v,v^1<<i,v^1<<i^1<<j,v^1<<j] for v in range(512) for i,j in itertools.combinations(range(5),2) if not {v,v^1<<i,v^1<<i^1<<j,v^1<<j}&avoid)
m=Model(record['word'],len(p)+4)
def var(v):return m.x[m.order.index(v>>5)][v&31]
allpositive = {var(v) for v in (a|set(cycle))}
path,cuts = m.decode(allpositive)
assert path==p and len(cuts)==1 and set(cuts[0])=={-var(v) for v in cycle}
all_vars=[v for row in m.x for v in row]
with Solver(name='cadical195',bootstrap_with=m.clauses) as solver:
    fixed=[v if v in allpositive else -v for v in all_vars]
    assert solver.solve(assumptions=fixed)
    solver.add_clause(cuts[0])
    assert not solver.solve(assumptions=fixed)
print(json.dumps(dict(path_edges=len(p)-1,cycle=cycle,before='SAT',after='UNSAT',cut=cuts[0])))
