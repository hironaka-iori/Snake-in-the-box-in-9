"""Inspect a continuous geometry relaxation before attempting a large SAT replay."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'work/solver_packages'),str(ROOT/'work/share_packages'),str(ROOT/'milestones/10-window-aggregate/scripts')]
import numpy as np
from ortools.linear_solver import pywraplp
from gen_lean_sat import TaggedEncoding
from wincert import window_from_dirs
enc=TaggedEncoding(window_from_dirs([0,1,2,3,4,0]),[(0,21),(0,21),(0,2),(0,21),(0,21)],radius=4)
variables=sorted(x for x,m in enc.meaning.items() if m[0] in ('p','e'));index={x:i for i,x in enumerate(variables)}
rows=[];cols=[];data=[];rhs=[];kinds=[]
for cl,tag in zip(enc.clauses,enc.tags):
    if tag[0] in ['first','zero','mono','step','over']:continue
    assert all(abs(x) in index for x in cl)
    r=len(rhs);rhs.append(sum(x<0 for x in cl)-1);kinds.append(tag[0])
    for lit in cl:rows.append(r);cols.append(index[abs(lit)]);data.append(-1 if lit>0 else 1)
ends=[index[x] for x in variables if enc.meaning[x][0]=='e']
r=len(rhs);rhs.append(2);kinds.append('end-count')
for x in ends:rows.append(r);cols.append(x);data.append(1)
def corners(i):
    v=enc.window[i];used={v^enc.window[i-1],v^enc.window[i+1]}
    return [index[enc.var[v^(1<<a)^(1<<b)]] for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used]
r=len(rhs);rhs.append(-19);kinds.append('middle-count')
for x in corners(3):rows.append(r);cols.append(x);data.append(-1)
objective=np.zeros(len(variables));mult=Counter(x for i in [1,2,4,5] for x in corners(i))
for x,n in mult.items():objective[x]=-n
solver=pywraplp.Solver.CreateSolver('GLOP');solver.SetTimeLimit(30000)
vs=[solver.NumVar(0,1,f'x{i}') for i in range(len(variables))]
cons=[solver.RowConstraint(-solver.infinity(),float(b),f'c{i}') for i,b in enumerate(rhs)]
for r,c,v in zip(rows,cols,data):cons[r].SetCoefficient(vs[c],float(v))
obj=solver.Objective()
for i,c in enumerate(objective):obj.SetCoefficient(vs[i],float(c))
obj.SetMinimization();start=time.monotonic();status=solver.Solve();success=status==pywraplp.Solver.OPTIMAL
out=dict(status='NUMERICAL_LP_DIAGNOSTIC',success=success,solver_status=status,
    variables=len(variables),constraints=len(rhs),constraint_kinds=dict(Counter(kinds)),seconds=time.monotonic()-start,
    scope='Continuous numerical relaxation only. A primal/dual solver status is not a proof about snakes.')
if success:
    x=np.array([v.solution_value() for v in vs]);dual=np.array([c.dual_value() for c in cons])
    lhs=np.bincount(np.array(rows),weights=np.array(data)*x[np.array(cols)],minlength=len(rhs))
    out.update(outer_count_lower=84+obj.Value(),max_primal_violation=float(np.max(lhs-np.array(rhs))),
        nonzero_dual_constraints=int(np.count_nonzero(np.abs(dual)>1e-8)))
    np.savez_compressed(HERE/'data/linear-relaxation.npz',x=x,dual=dual,reduced_costs=np.array([v.reduced_cost() for v in vs]))
(HERE/'data/linear-relaxation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
