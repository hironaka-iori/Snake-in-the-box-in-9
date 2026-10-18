"""Cost probe for linear-certificate branch and bound, not a formal proof."""
import sys,json,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[3]/'Snake in the Box/work/solver_packages'))
from ortools.linear_solver import pywraplp
data=json.loads(Path('work/lean/degree112.json').read_text())
clauses=[c for c in data['clauses'] if max(map(abs,c))<=244]
s=pywraplp.Solver.CreateSolver('GLOP')
vs=[None]+[s.NumVar(0,1,f'x{i}') for i in range(1,245)]
for c in clauses:s.Add(sum(vs[v] if v>0 else 1-vs[-v] for v in c)>=1)
s.Add(sum(vs[123:245])<=2)
s.Maximize(sum(vs[1:123]))
nodes=0;leaves=0;integral=0;start=time.time()
class Limit(Exception):pass
def visit(a):
    global nodes,leaves,integral
    nodes+=1
    if nodes>5000 or time.time()-start>120:raise Limit
    change=True
    while change:
        change=False
        for c in clauses:
            if any(a[abs(v)]==(1 if v>0 else 0) for v in c):continue
            unknown=[v for v in c if a[abs(v)]<0]
            if not unknown:leaves+=1;return
            if len(unknown)==1:
                v=unknown[0];a[abs(v)]=int(v>0);change=True
    for i in range(1,245):vs[i].SetBounds(0 if a[i]<0 else a[i],1 if a[i]<0 else a[i])
    status=s.Solve()
    if status==2 or (status==0 and s.Objective().Value()<82-1e-7):leaves+=1;return
    if status!=0:raise RuntimeError(status)
    fractional=[i for i in range(1,245) if 1e-7<vs[i].solution_value()<1-1e-7]
    if not fractional:
        integral+=1;print('FEASIBLE',s.Objective().Value(),flush=True);raise Limit
    i=min(fractional,key=lambda i:abs(vs[i].solution_value()-.5))
    for value in (0,1):
        b=a.copy();b[i]=value;visit(b)
try:
    visit([-1]*245);print('EXHAUSTED',nodes,leaves,time.time()-start,flush=True)
except Limit:print('LIMIT',nodes,leaves,integral,time.time()-start,flush=True)
