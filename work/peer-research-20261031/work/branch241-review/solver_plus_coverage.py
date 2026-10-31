from pathlib import Path
import json
from solver_plus import Solver,luby
from rup_check import check
H=Path(__file__).parent;rows=[]
assert [luby(i) for i in range(1,16)]==[1,1,2,1,1,2,4,1,1,2,1,1,2,4,8]
holes=6;v=lambda p,h:p*holes+h+1
cs=[[v(p,h) for h in range(holes)] for p in range(holes+1)]+[[-v(p,h),-v(q,h)] for h in range(holes) for p in range(holes+1) for q in range(p+1,holes+1)]
for restart in ('geometric','luby','lbd'):
 s=Solver(cs,binary=True,circular=True,minimize=True,restart=restart,seed=17);r=s.solve(seconds=10);assert r['status']=='UNSAT';r['proof']=check(cs,s.proof);assert r['binary_visits']>0 and r['minimized_literals']>0 and r['restarts']>0;rows.append(r)
(H/'solver_plus_coverage.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
