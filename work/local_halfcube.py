import json,time
from pathlib import Path
from exact_search import cp_model

reports=[]
for n in [4,5,6]:
    m=cp_model.CpModel()
    x=[m.new_bool_var(f'x{v}') for v in range(1<<n)]
    for v in range(1<<n):
        m.add(sum(x[v^(1<<k)] for k in range(n))<=2).only_enforce_if(x[v])
    for v in [0,1,3,7]:m.add(x[v]==1)
    m.add(sum(x)>=(1<<(n-1)))
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=30;s.parameters.num_search_workers=4
    t=time.monotonic();status=s.solve(m)
    r={'n':n,'forced_path':[0,1,3,7],'status':s.status_name(status),'seconds':time.monotonic()-t}
    if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
        r['selected']=[v for v in range(1<<n) if s.value(x[v])]
    reports.append(r);print(json.dumps(r),flush=True)
Path('outputs/local_halfcube.json').write_text(json.dumps(reports,indent=2))
