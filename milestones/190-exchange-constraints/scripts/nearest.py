from pathlib import Path
import json,itertools,time,sys,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/190-exchange-constraints';P=R/'milestones/188-dimensional-constructions';sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
p=json.loads((H/'data/middle95.json').read_text())['middle'];old=set(p);s,t=p[0],p[-1];d=s^t;NB=[{v^(1<<k) for k in range(8)} for v in range(256)]
p98=json.loads((P/'data/lower-dimensional-seeds.json').read_text())['8']['vertices'];target_on=[k for k in range(8) if d>>k&1];target_off=[k for k in range(8) if not d>>k&1];best=None
for src in [p98[:-1],p98[1:]]:
    for path in [src,src[::-1]]:
        path=[v^path[0] for v in path];delta=path[-1]
        if delta.bit_count()!=d.bit_count():continue
        source_on=[k for k in range(8) if delta>>k&1];source_off=[k for k in range(8) if not delta>>k&1]
        for a in itertools.permutations(target_on):
            for b in itertools.permutations(target_off):
                mapping=dict(zip(source_on+source_off,a+b));q=[s^sum(((v>>i)&1)<<j for i,j in mapping.items()) for v in path];overlap=len(set(q)&old)
                if best is None or overlap>best['overlap']:best={'overlap':overlap,'path':q}
assert best['path'][0]==s and best['path'][-1]==t
model=cp_model.CpModel();x=[model.new_bool_var('x'+str(v)) for v in range(256)];model.add(x[s]==1);model.add(x[t]==1);model.add(sum(x)==98)
for v in range(256):model.add(sum(x[u] for u in NB[v])==(1 if v in [s,t] else 2)).only_enforce_if(x[v])
deleted=[]
for i,(u,v) in enumerate(zip(p,p[1:])):
    z=model.new_bool_var('d'+str(i));model.add(z<=1-x[u]);model.add(z<=1-x[v]);model.add(z>=1-x[u]-x[v]);deleted.append(z)
added=[]
for u in range(256):
    if u in old:continue
    for v in sorted(NB[u]):
        if v<=u or v in old:continue
        z=model.new_bool_var(f'a{u}_{v}');model.add(z<=x[u]);model.add(z<=x[v]);model.add(z>=x[u]+x[v]-1);added.append(z)
model.add(sum(added)==sum(deleted)+2)
for a in range(8):
    for b in range(a+1,8):
        for u in range(256):
            if not (u&(1<<a) or u&(1<<b)):model.add(x[u]+x[u^(1<<a)]+x[u^(1<<b)]+x[u^(1<<a)^(1<<b)]<=3)
model.maximize(sum(x[v] for v in old));hint=set(best['path'])
for v in range(256):model.add_hint(x[v],int(v in hint))
solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=120;solver.parameters.max_memory_in_mb=512;solver.parameters.random_seed=190
start=time.monotonic();status=solver.solve(model);out={'status':solver.status_name(status),'seconds':time.monotonic()-start,'time_limit':120,'known_seed_best_overlap':best['overlap'],'known_seed_best_omissions':96-best['overlap'],'known_seed_path':best['path'],'objective_bound':solver.best_objective_bound,'scope':'Maximize overlap with the common95-edge path among98selectedQ8vertices with the same ports, exact path degrees, all square exclusions and exchange accounting. Longer disconnected cycles remain possible in this relaxation.'}
if status in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
    selected={v for v in range(256) if solver.value(x[v])};todo=[s];seen={s}
    while todo:
        u=todo.pop()
        for v in NB[u]&selected-seen:seen.add(v);todo.append(v)
    out['selected_vertices']=sorted(selected);out['old_vertices_retained']=len(selected&old);out['port_component_vertices']=len(seen)
    if len(seen)==98:
        path=[s];prev=None
        while path[-1]!=t:
            opts=(NB[path[-1]]&selected)-({prev} if prev is not None else set());assert len(opts)==1;v=next(iter(opts));assert v not in path;prev=path[-1];path.append(v)
        assert len(path)==98
        assert all(((path[i]^path[j]).bit_count()==1)==(j==i+1) for i in range(98) for j in range(i+1,98))
        out['middle_vertices']=path;out['actual_path']=True
    else:out['actual_path']=False
model.export_to_file(str(H/'data/nearest-replacement.pbtxt'));out['model_sha256']=hashlib.sha256((H/'data/nearest-replacement.pbtxt').read_bytes()).hexdigest();(H/'data/nearest-replacement.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if not isinstance(v,list)},indent=2),flush=True)
