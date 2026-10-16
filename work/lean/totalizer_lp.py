import sys,json,runpy
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[3]/'Snake in the Box/work/solver_packages'))
from ortools.linear_solver import pywraplp
d=runpy.run_path('work/lean/degree_cnf.py');r=d['r'];h=d['h'];n=len(r)
data=json.loads(Path('work/lean/totalizer112_82.json').read_text())
s=pywraplp.Solver.CreateSolver('GLOP')
vs=[None]+[s.NumVar(0,1,f'x{i}') for i in range(1,2*n+1)]
for c in data['clauses']:
    if max(map(abs,c))<=2*n:s.Add(sum(vs[v] if v>0 else 1-vs[-v] for v in c)>=1)
s.Add(sum(vs[n+1:])==2)
s.Maximize(sum(vs[1:n+1]));status=s.Solve()
print('maximum with square/parity endpoint clauses',status,s.Objective().Value(),flush=True)
for parity in (0,1):s.Add(sum(vs[i+1] for i,v in enumerate(r) if v.bit_count()%2==parity)==41)
status=s.Solve();print('with exact parity census',status,flush=True)
