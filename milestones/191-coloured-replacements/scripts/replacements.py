from pathlib import Path
import argparse,hashlib,json,sys,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/191-coloured-replacements'
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--omissions',type=int,required=True);ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--context',type=int);args=ap.parse_args()
p=json.loads((H/'data/middle95.json').read_text())['middle'];old=set(p);s,t=p[0],p[-1]
NB=[{v^(1<<k) for k in range(8)} for v in range(256)]
model=cp_model.CpModel();x=[model.new_bool_var('x'+str(v)) for v in range(256)]
model.add(x[s]==1);model.add(x[t]==1);model.add(sum(x)==98)
model.add(sum(x[v] for v in old)>=96-args.omissions)
for v in range(256):model.add(sum(x[u] for u in NB[v])==(1 if v in [s,t] else 2)).only_enforce_if(x[v])
# Opposite fixed endpoints give 49 selected vertices of each parity.
model.add(sum(x[v] for v in range(256) if v.bit_count()%2==0)==49)
if args.context is not None:
    row=json.loads((R/'milestones/189-middle-replacements/data/replacement-contexts.json').read_text())['rows'][args.context]
    assert row['middle']==p, 'Context must use the same labelled middle.'
    allowed=set(row['allowed'])
    for v in set(range(256))-allowed:model.add(x[v]==0)
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
squarecuts=0
for a in range(8):
    for b in range(a+1,8):
        for u in range(256):
            if u&(1<<a) or u&(1<<b):continue
            model.add(x[u]+x[u^(1<<a)]+x[u^(1<<b)]+x[u^(1<<a)^(1<<b)]<=3);squarecuts+=1
tag=f'omissions-at-most-{args.omissions}'+('' if args.context is None else f'-context{args.context:02d}')
modelpath=H/'data'/(tag+'.pbtxt');assert not modelpath.exists();model.export_to_file(str(modelpath))
start=time.monotonic();steps=[];cuts=[];solution=None;terminal='UNKNOWN'
while time.monotonic()-start<args.seconds:
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=max(.001,args.seconds-(time.monotonic()-start));solver.parameters.max_memory_in_mb=512;solver.parameters.random_seed=191
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
    cycles=[sorted(c) for c in components if s not in c];entry['component_sizes']=[len(c) for c in components];entry['omissions']=96-len(selected&old);entry['cycle_cuts_added']=len(cycles);steps.append(entry)
    if not cycles:
        path=[s];prev=None
        while path[-1]!=t:
            choices=(NB[path[-1]]&selected)-({prev} if prev is not None else set());assert len(choices)==1;v=next(iter(choices));assert v not in path;prev=path[-1];path.append(v)
        assert len(path)==98 and len(set(path)&old)>=96-args.omissions
        assert all(((path[i]^path[j]).bit_count()==1)==(j==i+1) for i in range(98) for j in range(i+1,98))
        solution=path;terminal='FEASIBLE';break
    for c in cycles:
        assert all(len(NB[v]&set(c))==2 for v in c)
        model.add(sum(x[v] for v in c)<=len(c)-1);cuts.append(c)
    print(json.dumps(entry),flush=True)
out={'status':terminal,'seconds':time.monotonic()-start,'time_limit':args.seconds,'max_omissions':args.omissions,'context':args.context,'square_cuts':squarecuts,'dynamic_cycle_cuts':cuts,'iterations':steps,'solution':solution,'initial_model_sha256':hashlib.sha256(modelpath.read_bytes()).hexdigest(),'middle_sha256':hashlib.sha256((H/'data/middle95.json').read_bytes()).hexdigest(),'scope':'98 selected Q8 vertices with the same ports; at most the specified omissions. Exact induced path degrees, colour balance, exchange edge identity and all square exclusions. Longer disconnected cycles are iteratively excluded. No deleted-interval restriction. External Q9 restrictions only if context is specified. Native solver result; no Lean contradiction certificate.'}
(H/'data'/(tag+'.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['solution','dynamic_cycle_cuts','iterations']},indent=2),flush=True)
