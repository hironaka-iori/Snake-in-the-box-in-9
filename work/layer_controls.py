import json
from pathlib import Path
from exact_search import model, cp_model
from check_snake import verify
seed=[0,1,3,7,6]
verify([0,1,2,0],3)
reports=[]
for root in [0,6]:
    for target in [2,3]:
        m,x,arcs=model(3,target,symmetry=False)
        for v in set(t^root for t in seed)-{0}: m.add(x[v]==0)
        s=cp_model.CpSolver();s.parameters.max_time_in_seconds=5
        status=s.solve(m)
        r={'dimension':3,'root':root,'target_partner_edges':target,'status':s.status_name(status)}
        if target==2:
            assert status in (cp_model.OPTIMAL,cp_model.FEASIBLE)
            path=[0]
            while True:
                nxt=[v for (u,v),a in arcs.items() if u==path[-1] and s.value(a)]
                if not nxt:break
                path.append(nxt[0])
            first=[v^root for v in seed]
            if first[-1]!=0:first.reverse()
            combined=first+[v+8 for v in path]
            checked=verify([(u^v).bit_length()-1 for u,v in zip(combined,combined[1:])],4)
            assert checked['edges']==7
            r['joined_vertices']=combined
        else: assert status==cp_model.INFEASIBLE
        reports.append(r)
Path('outputs/layer_controls.json').write_text(json.dumps(reports,indent=2))
print(json.dumps(reports,indent=2))
