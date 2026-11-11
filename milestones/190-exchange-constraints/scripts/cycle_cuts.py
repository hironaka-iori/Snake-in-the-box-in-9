from pathlib import Path
import json,sys,time,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/190-exchange-constraints';sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
p=json.loads((H/'data/middle95.json').read_text())['middle'];old=set(p);s,t=p[0],p[-1];NB=[{v^(1<<k) for k in range(8)} for v in range(256)];model=cp_model.CpModel();x=[model.new_bool_var('x'+str(v)) for v in range(256)]
model.add(x[s]==1);model.add(x[t]==1);model.add(sum(x)==98);model.add(sum(x[v] for v in old)==91)
for v in range(256):model.add(sum(x[u] for u in NB[v])==(1 if v in [s,t] else 2)).only_enforce_if(x[v])
deleted=[]
for i,(u,v) in enumerate(zip(p,p[1:])):
    z=model.new_bool_var('d'+str(i));model.add(z<=1-x[u]);model.add(z<=1-x[v]);model.add(z>=1-x[u]-x[v]);deleted.append(z)
# One/two deleted intervals were exhausted in separate native enumerations.
model.add(sum(deleted)<=2)
added=[]
for u in range(256):
    if u in old:continue
    for v in sorted(NB[u]):
        if v<=u or v in old:continue
        z=model.new_bool_var(f'a{u}_{v}');model.add(z<=x[u]);model.add(z<=x[v]);model.add(z>=x[u]+x[v]-1);added.append(z)
model.add(sum(added)==sum(deleted)+2)
squarecuts=0
for a in range(8):
    for b in range(a+1,8):
        for u in range(256):
            if u&(1<<a) or u&(1<<b):continue
            model.add(x[u]+x[u^(1<<a)]+x[u^(1<<b)]+x[u^(1<<a)^(1<<b)]<=3);squarecuts+=1
start=time.monotonic();steps=[];cuts=[];solution=None;terminal='UNKNOWN';last_selected=None
while time.monotonic()-start<120:
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=max(.001,120-(time.monotonic()-start));solver.parameters.max_memory_in_mb=512;solver.parameters.random_seed=190
    status=solver.solve(model);entry={'iteration':len(steps),'status':solver.status_name(status),'seconds':solver.wall_time,'branches':solver.num_branches,'conflicts':solver.num_conflicts}
    if status not in [cp_model.FEASIBLE,cp_model.OPTIMAL]:steps.append(entry);terminal=solver.status_name(status);break
    selected={v for v in range(256) if solver.value(x[v])};remaining=set(selected);components=[]
    while remaining:
        seed=min(remaining);component={seed};todo=[seed];remaining.remove(seed)
        while todo:
            u=todo.pop()
            for v in NB[u]&remaining:remaining.remove(v);component.add(v);todo.append(v)
        components.append(component)
    path_component=next(c for c in components if s in c);assert t in path_component
    cycles=[sorted(c) for c in components if s not in c];entry['component_sizes']=[len(c) for c in components];entry['cycle_cuts_added']=len(cycles);steps.append(entry)
    if not cycles:
        path=[s];prev=None
        while path[-1]!=t:
            choices=(NB[path[-1]]&selected)-({prev} if prev is not None else set());assert len(choices)==1;v=next(iter(choices));assert v not in path;prev=path[-1];path.append(v)
        assert len(path)==98 and len(set(path)&old)==91
        assert all(((path[i]^path[j]).bit_count()==1)==(j==i+1) for i in range(98) for j in range(i+1,98))
        solution=path;terminal='FEASIBLE';break
    for c in cycles:
        assert all(len(NB[v]&set(c))==2 for v in c)
        model.add(sum(x[v] for v in c)<=len(c)-1);cuts.append(c)
    print(json.dumps(entry),flush=True)
tag='five-omissions-cycle-cuts';model.export_to_file(str(H/'data'/(tag+'.pbtxt')))
out={'status':terminal,'seconds':time.monotonic()-start,'time_limit':120,'square_cuts':squarecuts,'dynamic_cycle_cuts':cuts,'iterations':steps,'solution':solution,'model_sha256':hashlib.sha256((H/'data'/(tag+'.pbtxt')).read_bytes()).hexdigest(),'scope':'Exactly five original vertices omitted in at least three deleted intervals (deleted internal edges<=2). Degree equations, all square cuts, and iterative cuts on disconnected induced cycles. The one/two-interval cases were separately enumerated. No externalQ9restrictions.'}
(H/'data'/(tag+'.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['solution','dynamic_cycle_cuts','iterations']},indent=2),flush=True)
print('ITERATIONS',len(steps),'DYNAMIC_CUTS',len(cuts),flush=True)
