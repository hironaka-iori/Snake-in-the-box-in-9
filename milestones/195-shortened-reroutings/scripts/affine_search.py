"""Seek a longer path in the 128-vertex quotient, with connected-flow constraints."""
from pathlib import Path
import argparse,hashlib,json,sys,threading,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--vertices',type=int,default=50);ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--tag',default='affine50');ap.add_argument('--omissions',type=int,default=4);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=H/'data/symmetry-comparison.json';raw=source.read_bytes();comparison=json.loads(raw);case=comparison['candidates'][0]
profilepath=H/'data/forest-profiles.json';profile=json.loads(profilepath.read_bytes());seedpath=profile['bank_forests'][case['forest']]['paths'][0]
def g(v):return sum(((v>>i)&1)<<case['permutation'][i] for i in range(8))^case['translation']
def orb(v):return min(v,g(v))
V=sorted({orb(v) for v in range(256)})
N={v:sorted({orb(v^(1<<k)) for k in range(8)}) for v in V}
assert len(V)==128 and all(v not in N[v] for v in V)
hint=[orb(v) for v in seedpath];root=hint[0]
assert len(set(hint))==48 and all(((hint[j] in N[v])==(j==i+1)) for i,v in enumerate(hint) for j in range(i+1,len(hint)))
bad={tuple(sorted([v,orb(v^(1<<k))])) for v in V for k in range(8) if sum(orb(v^(1<<j))==orb(v^(1<<k)) for j in range(8))>1}
m=cp_model.CpModel();x={v:m.new_bool_var('x'+str(v)) for v in V};end={v:m.new_bool_var('end'+str(v)) for v in V};edge={}
for v in V:
 m.add(end[v]<=x[v])
 for w in N[v]:
  if v<w:
   y=m.new_bool_var('e'+str(v)+'_'+str(w));edge[v,w]=y;m.add(y<=x[v]);m.add(y<=x[w]);m.add(y>=x[v]+x[w]-1)
for v in V:m.add(sum(edge[min(v,w),max(v,w)] for w in N[v])==2*x[v]-end[v])
m.add(sum(x.values())==a.vertices);m.add(sum(end.values())==2);m.add(end[root]==1)
m.add(sum(x[v] for v in hint)>=len(hint)-a.omissions)
for v,w in bad:m.add(x[v]+x[w]<=1)
assert all(g(g(v))==v and (v^g(v)).bit_count()>=2 for v in range(256))
flow={}
for v in V:
 for w in N[v]:
  f=m.new_int_var(0,a.vertices-1,'f'+str(v)+'_'+str(w));flow[v,w]=f;m.add(f<=(a.vertices-1)*edge[min(v,w),max(v,w)])
for v in V:m.add(sum(flow[w,v]-flow[v,w] for w in N[v])==(1-a.vertices if v==root else x[v]))
triangles=0;squares=set()
for v in V:
 for w in N[v]:
  if w<=v:continue
  for z in set(N[v])&set(N[w]):
   if z>w:m.add(x[v]+x[w]+x[z]<=2);triangles+=1
  for z in N[w]:
   if z==v:continue
   for t in set(N[z])&set(N[v]):
    if t!=w:squares.add(tuple(sorted([v,w,z,t])))
for sq in squares:m.add(sum(x[v] for v in sq)<=3)
for v in V:m.add_hint(x[v],int(v in hint))
modelpath=H/'data'/(a.tag+'.pbtxt');m.export_to_file(str(modelpath))
s=cp_model.CpSolver();s.parameters.num_search_workers=1;s.parameters.max_time_in_seconds=a.seconds;s.parameters.max_memory_in_mb=256
samples=[];stop=[];done=threading.Event()
def monitor():
 while not done.wait(1):
  snap=snapshot();samples.append(snap)
  if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:stop.append('RESOURCE_LIMIT');s.stop_search();return
t=threading.Thread(target=monitor,daemon=True);t.start();start=time.monotonic();status=s.solve(m);done.set();t.join()
witness=None
if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
 selected={v for v in V if s.value(x[v])};path=[root]
 while True:
  choices=[v for v in N[path[-1]] if v in selected and (len(path)<2 or v!=path[-2])]
  if not choices:break
  assert len(choices)==1;path.append(choices[0]);assert len(path)<=len(selected)
 assert len(path)==a.vertices and len(set(path))==len(path)
 assert all(((path[j] in N[v])==(j==i+1)) for i,v in enumerate(path) for j in range(i+1,len(path)))
 lift=[path[0]]
 for z in path[1:]:
  options=[lift[-1]^(1<<k) for k in range(8) if orb(lift[-1]^(1<<k))==z];assert len(options)==1;lift.append(options[0])
 partner=[g(v) for v in lift]
 assert len(set(lift+partner))==2*len(lift) and all((u^v).bit_count()!=1 for u in lift for v in partner)
 for p in [lift,partner]:assert all((((v^p[j]).bit_count()==1)==(j==i+1)) for i,v in enumerate(p) for j in range(i+1,len(p)))
 witness=dict(quotient_path=path,paths=[lift,partner],fixed_face_vertices=2*len(lift))
out=dict(status=stop[0] if stop else s.status_name(status),seconds=time.monotonic()-start,arguments=vars(a),root=root,
 affine_case=case,profile_sha256=hashlib.sha256(profilepath.read_bytes()).hexdigest(),bad_edges=len(bad),quotient_vertices=len(V),triangles=triangles,squares=len(squares),source_sha256=hashlib.sha256(raw).hexdigest(),model_sha256=hashlib.sha256(modelpath.read_bytes()).hexdigest(),
 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),resource_gate=gate,resource_samples=samples,witness=witness,
 branches=s.num_branches,conflicts=s.num_conflicts,scope='Exact-size induced path in the observed-symmetry quotient with one endpoint fixed at the displayed root. Connectivity enforced by directed flow. Forbidden double-lift edges are excluded. At most the specified original vertices may be omitted. This does not address all Q8 two-path forests.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status=out['status'],seconds=out['seconds'],witness=bool(witness),triangles=triangles,squares=len(squares))),flush=True)
