"""Exact degree relaxation, adding valid cycle exclusions until connected."""
from pathlib import Path
import argparse,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,default=260);ap.add_argument('--per-base',type=float,default=60);ap.add_argument('--per-query',type=float,default=5);ap.add_argument('--bases',default='139,7,6,0');ap.add_argument('--exchanges',type=int,default=2);a=ap.parse_args()
source=H/'data/bases.json';raw=json.loads(source.read_bytes());assert all(sha(p)==h for p,h in raw['pins'].items())
requested=[int(x) for x in a.bases.split(',')];assert len(set(requested))==len(requested) and 0<=a.exchanges<=96
N={v:[v^(1<<j) for j in range(9)] for v in range(512)}
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
out=dict(status='RUNNING',arguments=vars(a),source_sha256=sha(source),script_sha256=sha(__file__),results=[],witness=None,scope='Exact selected degrees and two majority endpoints produce one path plus zero or more disjoint induced cycles. Every observed cycle yields a valid occupancy inequality. Only a connected193vertex sequence is a witness. INFEASIBLE excludes this prescribed minority exchange family; UNKNOWN or budget exhaustion remains unresolved.')
def save():dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
started=time.monotonic();save()
for bid in requested:
 if time.monotonic()-started>=a.seconds:break
 U=set(raw['bases'][bid]['vertices']);assert raw['bases'][bid]['id']==bid and len(U)==96
 parity=next(iter(U)).bit_count()%2;minor=[v for v in range(512) if v.bit_count()%2==parity];major=[v for v in range(512) if v.bit_count()%2!=parity];assert U<=set(minor)
 m=cp_model.CpModel();x={v:m.new_bool_var(f'x{v}') for v in range(512)};ep={v:m.new_bool_var(f'e{v}') for v in major}
 m.add(sum(x[v] for v in minor)==96);m.add(sum(x[v] for v in major)==97);m.add(sum(x[v] for v in sorted(U))==96-a.exchanges);m.add(sum(ep.values())==2)
 for v in major:m.add(ep[v]<=x[v])
 for v in range(512):m.add(sum(x[w] for w in N[v])+(ep[v] if v in ep else 0)==2).only_enforce_if(x[v])
 row=dict(base=bid,exchanges=a.exchanges,status='RUNNING',iterations=[],cuts=[]);out['results'].append(row);seen=set();base_start=time.monotonic();iteration=0
 while time.monotonic()-base_start<a.per_base and time.monotonic()-started<a.seconds:
  model=H/'data'/f'{a.tag}-{bid:03d}-{iteration:04d}.pbtxt';assert not model.exists();m.export_to_file(str(model))
  solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_memory_in_mb=256;solver.parameters.max_time_in_seconds=min(a.per_query,max(.001,a.per_base-(time.monotonic()-base_start)),max(.001,a.seconds-(time.monotonic()-started)));solver.parameters.random_seed=0;solver.parameters.linearization_level=0
  code=solver.solve(m);step=dict(iteration=iteration,status=solver.status_name(code),model=model.name,model_sha256=sha(model),seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts,cut_count_before=len(row['cuts']));row['iterations'].append(step)
  if code==cp_model.INFEASIBLE:row['status']='INFEASIBLE';break
  if code not in [cp_model.OPTIMAL,cp_model.FEASIBLE]:row['status']=solver.status_name(code);break
  selected={v for v in range(512) if solver.value(x[v])};ends={v for v in major if solver.value(ep[v])};assert len(selected)==193 and len(ends)==2 and ends<=selected
  adj={v:set(N[v])&selected for v in selected};assert all(len(adj[v])==2-int(v in ends) for v in selected)
  assert len(selected&set(minor))==96 and len(U-selected)==len((selected&set(minor))-U)==a.exchanges
  unseen=set(selected);components=[]
  while unseen:
   todo=[min(unseen)];C=set()
   while todo:
    v=todo.pop()
    if v in C:continue
    C.add(v);unseen.discard(v);todo.extend(adj[v]-C)
   components.append(C)
  paths=[C for C in components if C&ends];cycles=[C for C in components if not C&ends]
  assert len(paths)==1 and ends<=paths[0]
  step.update(selected=sorted(selected),endpoints=sorted(ends),component_sizes=sorted(map(len,components)))
  if not cycles:
   path=[min(ends)];previous=None
   while len(path)<193:
    options=adj[path[-1]]-({previous} if previous is not None else set());assert len(options)==1
    previous=path[-1];path.append(next(iter(options)));assert len(set(path))==len(path)
   assert path[-1] in ends and set(path)==selected
   assert all(((v^path[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(path) for j in range(i+1,len(path)))
   out['witness']=dict(base=bid,edges=192,path=path,minority_class=sorted(selected&set(minor)),removed=sorted(U-selected),inserted=sorted((selected&set(minor))-U));row['status']='WITNESS';break
  for C in cycles:
   assert len(C)>=4 and all(len(adj[v])==2 for v in C)
   key=tuple(sorted(C));assert key not in seen;seen.add(key)
   m.add(sum(x[v] for v in key)<=len(key)-1);row['cuts'].append(dict(vertices=list(key),from_iteration=iteration))
  iteration+=1;save()
 if row['status']=='RUNNING':row['status']='TIME_LIMIT'
 row['seconds']=time.monotonic()-base_start;save();print(json.dumps(dict(base=bid,status=row['status'],queries=len(row['iterations']),cuts=len(row['cuts']),seconds=row['seconds'])),flush=True)
 if out['witness']:break
out['status']='WITNESS' if out['witness'] else 'COMPLETE_QUERY_BATCH' if len(out['results'])==len(requested) else 'TIME_LIMIT';out['seconds']=time.monotonic()-started;save();print(json.dumps(dict(status=out['status'],results=[{k:r[k] for k in ['base','status']} for r in out['results']],witness=out['witness'])),flush=True)
