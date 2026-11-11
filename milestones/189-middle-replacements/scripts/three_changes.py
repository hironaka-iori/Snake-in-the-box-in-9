from pathlib import Path
import sys,json,time,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements';sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
row=json.loads((H/'data/replacement-contexts.json').read_text())['rows'][0];old=row['middle'];s,t=old[0],old[-1];model=cp_model.CpModel();x=[model.new_bool_var('x'+str(v)) for v in range(256)];arcs=[(v,v,x[v].Not()) for v in range(256)];directed={}
for u in range(256):
    for k in range(8):
        v=u^(1<<k)
        if v<=u:continue
        a=model.new_bool_var(f'a{u}_{v}');b=model.new_bool_var(f'a{v}_{u}');directed[u,v]=a;directed[v,u]=b;arcs.extend([(u,v,a),(v,u,b)])
        model.add(a+b<=x[u]);model.add(a+b<=x[v]);model.add(a+b>=x[u]+x[v]-1)
model.add(x[s]==1);model.add(x[t]==1);arcs.append((t,s,True));model.add_circuit(arcs);model.add(sum(x)==98);model.add(sum(x[v] for v in old)==93)
for v,b in enumerate(x):model.add_hint(b,int(v in old))
model.export_to_file(str(H/'data/three-changes.pbtxt'));solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=90;solver.parameters.max_memory_in_mb=512;solver.parameters.random_seed=189
start=time.monotonic();status=solver.solve(model);out={'status':solver.status_name(status),'seconds':time.monotonic()-start,'time_limit':90,'branches':solver.num_branches,'conflicts':solver.num_conflicts,'model_sha256':hashlib.sha256((H/'data/three-changes.pbtxt').read_bytes()).hexdigest(),'scope':'A97-edgeQ8path with the same ports, retaining exactly93 of the96 vertices of the common95-edge path. All outside vertices are available; no Q9 outer restrictions.'}
if status in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
    path=[s]
    while path[-1]!=t:
        opts=[v for (u,v),b in directed.items() if u==path[-1] and solver.value(b)];assert len(opts)==1 and opts[0] not in path;path.append(opts[0])
    assert len(path)==98 and len(set(path)&set(old))==93
    assert all(((path[i]^path[j]).bit_count()==1)==(j==i+1) for i in range(98) for j in range(i+1,98))
    out.update(middle_vertices=path,removed_vertices=sorted(set(old)-set(path)),added_vertices=sorted(set(path)-set(old)))
(H/'data/three-changes.json').write_text(json.dumps(out,indent=2)+'\n');(H/'scripts/three_changes.py').write_bytes(Path(__file__).read_bytes());print(json.dumps({k:v for k,v in out.items() if not isinstance(v,list)},indent=2),flush=True)
