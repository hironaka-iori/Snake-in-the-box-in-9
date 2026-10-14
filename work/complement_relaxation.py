import json,time
from pathlib import Path
from exact_search import cp_model
seed=json.loads(Path('outputs/snake8_witness.json').read_text())['vertex_sequence']
reports=[]
for root in [seed[0],seed[-1]]:
    blocked={v^root for v in seed}-{0}
    m=cp_model.CpModel()
    x=[m.new_bool_var(f'x{v}') for v in range(256)]
    for v in blocked: m.add(x[v]==0)
    m.add(x[0]==1)
    for v in range(256):
        m.add(sum(x[v^(1<<k)] for k in range(8))<= (1 if v==0 else 2)).only_enforce_if(x[v])
    m.maximize(sum(x))
    s=cp_model.CpSolver()
    s.parameters.max_time_in_seconds=30
    s.parameters.num_search_workers=4
    start=time.monotonic();status=s.solve(m)
    r={'root':root,'status':s.status_name(status),'selected_vertices':s.objective_value,
       'upper_bound':s.best_objective_bound,'elapsed_seconds':time.monotonic()-start}
    reports.append(r)
    print(json.dumps(r),flush=True)
Path('outputs/complement_relaxation.json').write_text(json.dumps(reports,indent=2))
