import sys,json
from pathlib import Path
from itertools import combinations
sys.path.insert(0,str(Path(__file__).resolve().parents[3]/'Snake in the Box/work/solver_packages'))
from ortools.linear_solver import pywraplp
data=json.loads(Path('work/lean/degree112.json').read_text())
s=pywraplp.Solver.CreateSolver('GLOP')
vs=[None]+[s.NumVar(0,1,f'x{i}') for i in range(1,data['variables']+1)]
for c in data['clauses']:
    s.Add(sum(vs[v] if v>0 else 1-vs[-v] for v in c)>=1)
status=s.Solve()
print('CNF LP status',status,'0=optimal 2=infeasible',flush=True)
s=pywraplp.Solver.CreateSolver('GLOP')
vs=[None]+[s.NumVar(0,1,f'x{i}') for i in range(1,245)]
for c in data['clauses']:
    if max(map(abs,c))<=244:
        s.Add(sum(vs[v] if v>0 else 1-vs[-v] for v in c)>=1)
s.Maximize(sum(vs[1:123]));status=s.Solve()
print('direct count LP maximum',s.Objective().Value(),status,flush=True)
s.Add(sum(vs[123:245])<=2)
status=s.Solve()
print('with endpoint budget',s.Objective().Value(),status,flush=True)
