from pathlib import Path
import argparse,hashlib,json,sys,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--omissions',type=int,required=True);ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--crossings',type=int,default=2);ap.add_argument('--gain',type=int,default=1);args=ap.parse_args()
p=json.loads((H/'data/seed.json').read_text())['path'];old=set(p);NB=[{v^(1<<k) for k in range(9)} for v in range(512)];target=192+args.gain
model=cp_model.CpModel();x=[model.new_bool_var('x'+str(v)) for v in range(512)];ep=[model.new_bool_var('ep'+str(v)) for v in range(512)]
model.add(sum(x)==target);model.add(sum(x[v] for v in old)>=192-args.omissions);model.add(sum(ep)==2)
for v in range(512):
    model.add(ep[v]<=x[v]);model.add(sum(x[u] for u in NB[v])==2-ep[v]).only_enforce_if(x[v])
if args.gain%2==1:
    majority=model.new_bool_var('majority_even');model.add(sum(x[v] for v in range(512) if v.bit_count()%2==0)==target//2+majority);model.add(sum(ep[v] for v in range(512) if v.bit_count()%2==0)==2*majority)
else:model.add(sum(x[v] for v in range(512) if v.bit_count()%2==0)==target//2)
cross=[]
if args.crossings>=0:
    for v in range(256):
        y=model.new_bool_var('cross'+str(v));model.add(y<=x[v]);model.add(y<=x[v+256]);model.add(y>=x[v]+x[v+256]-1);cross.append(y)
    model.add(sum(cross)==args.crossings)
deleted=[]
for i,(u,v) in enumerate(zip(p,p[1:])):
    y=model.new_bool_var('d'+str(i));model.add(y<=1-x[u]);model.add(y<=1-x[v]);model.add(y>=1-x[u]-x[v]);deleted.append(y)
added=[]
for u in range(512):
    if u in old:continue
    for v in sorted(NB[u]):
        if v<=u or v in old:continue
        y=model.new_bool_var(f'a{u}_{v}');model.add(y<=x[u]);model.add(y<=x[v]);model.add(y>=x[u]+x[v]-1);added.append(y)
model.add(sum(added)+sum(ep[v] for v in range(512) if v not in old)==sum(deleted)+args.gain+2-x[p[0]]-x[p[-1]])
squarecuts=0
for a in range(9):
    for b in range(a+1,9):
        for u in range(512):
            if u&(1<<a) or u&(1<<b):continue
            model.add(x[u]+x[u^(1<<a)]+x[u^(1<<b)]+x[u^(1<<a)^(1<<b)]<=3);squarecuts+=1
tag=f'gain{args.gain}-omit{args.omissions}-cross{args.crossings}';pathmodel=H/'data'/(tag+'.pbtxt');assert not pathmodel.exists();model.export_to_file(str(pathmodel));start=time.monotonic();steps=[];cuts=[];solution=None;status_name='UNKNOWN'
while time.monotonic()-start<args.seconds:
    solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_time_in_seconds=max(.001,args.seconds-(time.monotonic()-start));solver.parameters.max_memory_in_mb=512;solver.parameters.random_seed=192
    status=solver.solve(model);entry={'iteration':len(steps),'status':solver.status_name(status),'seconds':solver.wall_time,'branches':solver.num_branches,'conflicts':solver.num_conflicts}
    if status not in [cp_model.FEASIBLE,cp_model.OPTIMAL]:steps.append(entry);status_name=solver.status_name(status);break
    chosen={v for v in range(512) if solver.value(x[v])};ends=[v for v in range(512) if solver.value(ep[v])];assert len(ends)==2;remaining=set(chosen);components=[]
    while remaining:
        seed=min(remaining);part={seed};todo=[seed];remaining.remove(seed)
        while todo:
            u=todo.pop()
            for v in NB[u]&remaining:remaining.remove(v);part.add(v);todo.append(v)
        components.append(part)
    portpart=next(c for c in components if ends[0] in c);assert ends[1] in portpart;cycles=[sorted(c) for c in components if ends[0] not in c];entry.update(component_sizes=[len(c) for c in components],omissions=len(old-chosen),endpoints=ends,cycle_cuts_added=len(cycles));steps.append(entry)
    if not cycles:
        q=[ends[0]];previous=None
        while q[-1]!=ends[1]:
            options=(NB[q[-1]]&chosen)-({previous} if previous is not None else set());assert len(options)==1;v=next(iter(options));assert v not in q;previous=q[-1];q.append(v)
        assert len(q)==target and len(old-set(q))<=args.omissions
        assert all(((q[i]^q[j]).bit_count()==1)==(j==i+1) for i in range(target) for j in range(i+1,target))
        solution=q;status_name='FEASIBLE';break
    for c in cycles:model.add(sum(x[v] for v in c)<=len(c)-1);cuts.append(c)
    print(json.dumps(entry),flush=True)
out={'status':status_name,'seconds':time.monotonic()-start,'time_limit':args.seconds,'target_edges':target-1,'max_omissions':args.omissions,'coordinate8_crossings':args.crossings if args.crossings>=0 else 'unrestricted','square_cuts':squarecuts,'endpoint_correction_imposed':True,'iterations':steps,'dynamic_cycle_cuts':cuts,'solution':solution,'model_sha256':hashlib.sha256(pathmodel.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seed_sha256':hashlib.sha256((H/'data/seed.json').read_bytes()).hexdigest(),'scope':'Both endpoints, both faces and crossing vertices may change. At most r old vertices omitted. Exact induced degrees, colour constraints, corrected exchange edge identity and all squares. Longer cycle components are iteratively cut. Crossing count fixed only when specified. No Lean contradiction certificate.'}
(H/'data'/(tag+'.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['iterations','dynamic_cycle_cuts','solution']},indent=2),flush=True)
