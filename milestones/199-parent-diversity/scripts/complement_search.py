"""An arbitrary induced Q7 path disjoint from the fixed published parent."""
from pathlib import Path
import argparse,hashlib,json,sys,threading,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--vertices',type=int,default=49);ap.add_argument('--seconds',type=float,default=60);ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=source.read_bytes();p=json.loads(raw)['7']['vertices'];S=set(p)
V=sorted(set(range(128))-S);N={v:[v^(1<<k) for k in range(7) if v^(1<<k) in V] for v in V}
m=cp_model.CpModel();x={v:m.new_bool_var('x'+str(v)) for v in V};arcs=[(v,v,x[v].Not()) for v in V];directions={}
for v in V:
 for w in N[v]:
  if v<w:
   f=m.new_bool_var('a'+str(v)+'_'+str(w));b=m.new_bool_var('a'+str(w)+'_'+str(v))
   directions[v,w]=f;directions[w,v]=b;arcs.extend([(v,w,f),(w,v,b)])
   m.add(f+b<=x[v]);m.add(f+b<=x[w]);m.add(f+b>=x[v]+x[w]-1)
starts={};ends={}
for v in V:
 starts[v]=m.new_bool_var('s'+str(v));ends[v]=m.new_bool_var('t'+str(v))
 m.add(starts[v]<=x[v]);m.add(ends[v]<=x[v]);arcs.extend([(128,v,starts[v]),(v,128,ends[v])])
m.add_circuit(arcs);m.add(sum(x.values())==a.vertices)
m.add(sum(v*starts[v] for v in V)<sum(v*ends[v] for v in V))
balance=sum((1 if v.bit_count()%2==0 else -1)*x[v] for v in V)
m.add(balance>=-(a.vertices%2));m.add(balance<=a.vertices%2)
cuts=0
for v in V:
 for i in range(7):
  for j in range(i+1,7):
   sq=[v,v^(1<<i),v^(1<<j),v^(1<<i)^(1<<j)]
   if v==min(sq) and all(z in x for z in sq):m.add(sum(x[z] for z in sq)<=3);cuts+=1
modelpath=H/'data'/(a.tag+'.pbtxt');m.export_to_file(str(modelpath))
s=cp_model.CpSolver();s.parameters.num_search_workers=1;s.parameters.max_time_in_seconds=a.seconds;s.parameters.max_memory_in_mb=256
samples=[];stop=[];done=threading.Event()
def monitor():
 while not done.wait(1):
  snap=snapshot();samples.append(snap)
  if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:stop.append('RESOURCE_LIMIT');s.stop_search();return
t=threading.Thread(target=monitor,daemon=True);t.start();start=time.monotonic();code=s.solve(m);done.set();t.join();witness=None
if code in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
 q=[v for v in V if s.value(starts[v])];assert len(q)==1
 while not s.value(ends[q[-1]]):
  opts=[v for v in N[q[-1]] if s.value(directions[q[-1],v])];assert len(opts)==1;q.append(opts[0]);assert len(q)<=a.vertices
 assert len(q)==a.vertices and len(set(q))==len(q) and not S.intersection(q)
 assert all(((u^q[j]).bit_count()==1)==(j==i+1) for i,u in enumerate(q) for j in range(i+1,len(q)))
 paths=[p,[v+128 for v in q]]
 assert all((u^v).bit_count()!=1 for u in paths[0] for v in paths[1])
 witness=dict(paths=paths,fixed_face_vertices=len(p)+len(q),complement_path=q)
out=dict(status=stop[0] if stop else s.status_name(code),seconds=time.monotonic()-start,arguments=vars(a),allowed_vertices=len(V),allowed_edges=sum(map(len,N.values()))//2,square_cuts=cuts,branches=s.num_branches,conflicts=s.num_conflicts,witness=witness,source_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),model_sha256=hashlib.sha256(modelpath.read_bytes()).hexdigest(),resource_gate=gate,resource_samples=samples,scope='All induced paths of the target size in the complement of the one fixed published51-vertex Q7 parent; connected circuit with one dummy vertex. No seed overlap or symmetry restriction on the second path. Native solver result without a Lean contradiction certificate.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','seconds','allowed_vertices','allowed_edges','branches','conflicts']}),flush=True)
