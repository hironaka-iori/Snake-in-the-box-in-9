"""Choose two minority-class replacements and an entire induced Q9 path jointly."""
from pathlib import Path
import argparse,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,default=260);ap.add_argument('--per-query',type=float,default=60);ap.add_argument('--bases',default='139,7,6,0');ap.add_argument('--exchanges',type=int,default=2);a=ap.parse_args()
source=H/'data/bases.json';raw=json.loads(source.read_bytes());assert all(sha(p)==h for p,h in raw['pins'].items())
requested=[int(x) for x in a.bases.split(',')];assert len(set(requested))==len(requested)
assert 0<=a.exchanges<=96
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
out=dict(status='RUNNING',arguments=vars(a),source_sha256=sha(source),script_sha256=sha(__file__),results=[],witness=None,scope='Exactly96 minority and97 majority cubevertices, prescribed number of replacements of one saved96class. Optional-vertex circuit through a dummy; each selected cube adjacency must be used. All other class vertices, order and endpoints free. Native INFEASIBLE is restricted; UNKNOWN is unresolved.')
def save():dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
started=time.monotonic();save()
for bid in requested:
 if time.monotonic()-started>=a.seconds:break
 base=raw['bases'][bid];assert base['id']==bid;U=set(base['vertices']);assert len(U)==96
 parity=next(iter(U)).bit_count()%2;minor=[v for v in range(512) if v.bit_count()%2==parity];major=[v for v in range(512) if v.bit_count()%2!=parity]
 assert U<=set(minor)
 m=cp_model.CpModel();selected={v:m.new_bool_var(f'x{v}') for v in range(512)};arcs=[(v,v,selected[v].Not()) for v in range(512)];directions={}
 for v in range(512):
  for j in range(9):
   w=v^(1<<j)
   if v>=w:continue
   f=m.new_bool_var(f'a{v}_{w}');b=m.new_bool_var(f'a{w}_{v}');directions[v,w]=f;directions[w,v]=b
   arcs.extend([(v,w,f),(w,v,b)])
   m.add(f+b<=selected[v]);m.add(f+b<=selected[w]);m.add(f+b>=selected[v]+selected[w]-1)
 starts={v:m.new_bool_var(f's{v}') for v in major};ends={v:m.new_bool_var(f't{v}') for v in major}
 for v in major:
  m.add(starts[v]<=selected[v]);m.add(ends[v]<=selected[v]);arcs.extend([(512,v,starts[v]),(v,512,ends[v])])
 m.add_circuit(arcs);m.add(sum(selected[v] for v in minor)==96);m.add(sum(selected[v] for v in major)==97)
 m.add(sum(selected[v] for v in sorted(U))==96-a.exchanges)
 model=H/'data'/f'{a.tag}-{bid:03d}.pbtxt';assert not model.exists();m.export_to_file(str(model))
 row=dict(base=bid,exchanges=a.exchanges,status='RUNNING',model=model.name,model_sha256=sha(model),variables=len(m.proto.variables),constraints=len(m.proto.constraints));out['results'].append(row);save()
 solver=cp_model.CpSolver();solver.parameters.num_search_workers=1;solver.parameters.max_memory_in_mb=256;solver.parameters.max_time_in_seconds=min(a.per_query,max(.001,a.seconds-(time.monotonic()-started)));solver.parameters.random_seed=0
 code=solver.solve(m);row.update(status=solver.status_name(code),seconds=solver.wall_time,branches=solver.num_branches,conflicts=solver.num_conflicts,response_stats=solver.response_stats())
 if code in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
  picked={v for v in range(512) if solver.value(selected[v])};first=[v for v in major if solver.value(starts[v])];last=[v for v in major if solver.value(ends[v])];assert len(first)==len(last)==1
  path=first.copy()
  while path[-1]!=last[0]:
   opts=[w for w in (path[-1]^(1<<j) for j in range(9)) if solver.value(directions[path[-1],w])];assert len(opts)==1
   path.append(opts[0]);assert len(path)<=193
  assert len(path)==len(set(path))==193 and set(path)==picked
  assert all(((v^path[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(path) for j in range(i+1,len(path)))
  gotminor=picked&set(minor);assert len(gotminor)==96 and len(U-gotminor)==len(gotminor-U)==a.exchanges
  out['witness']=dict(base=bid,edges=192,path=path,minority_class=sorted(gotminor),removed=sorted(U-gotminor),inserted=sorted(gotminor-U));row['status']='WITNESS';save();break
 save();print(json.dumps({k:row[k] for k in ['base','status','seconds','branches','conflicts']}),flush=True)
out['status']='WITNESS' if out['witness'] else 'COMPLETE_QUERY_BATCH' if len(out['results'])==len(requested) else 'TIME_LIMIT'
out['seconds']=time.monotonic()-started;save();print(json.dumps(dict(status=out['status'],results=[{k:r[k] for k in ['base','status']} for r in out['results']],witness=out['witness'])),flush=True)
