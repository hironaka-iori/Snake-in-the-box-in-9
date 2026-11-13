"""Two variable induced Q7 paths near a minimum-overlap seed placement."""
from pathlib import Path
import argparse,hashlib,json,sys,threading,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--case',type=int,choices=[0,1],required=True);ap.add_argument('--omissions',type=int,required=True);ap.add_argument('--seconds',type=float,default=60);ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=source.read_bytes();p=json.loads(raw)['7']['vertices']
placement=R/'milestones/199-parent-diversity/data/all-isometries-published50.json';c=json.loads(placement.read_bytes())['rows'][0]['minimum_examples'][a.case]
def h(v):return sum(((v>>i)&1)<<c['permutation'][i] for i in range(7))^c['translation']
assert all(h(h(v))==v for v in range(128))
seeds=[p,[h(v) for v in p]];assert len(set(seeds[0])&set(seeds[1]))==2
N={v:[v^(1<<i) for i in range(7)] for v in range(128)}
m=cp_model.CpModel();xs=[];starts=[];ends=[];directions=[];omissions=[];squares=0
for k in range(2):
 x={v:m.new_bool_var(f'x{k}_{v}') for v in N};st={};en={};di={};arcs=[(v,v,x[v].Not()) for v in N]
 for v in N:
  for w in N[v]:
   if v<w:
    f=m.new_bool_var(f'a{k}_{v}_{w}');b=m.new_bool_var(f'a{k}_{w}_{v}');di[v,w]=f;di[w,v]=b
    arcs.extend([(v,w,f),(w,v,b)]);m.add(f+b<=x[v]);m.add(f+b<=x[w]);m.add(f+b>=x[v]+x[w]-1)
 for v in N:
  st[v]=m.new_bool_var(f's{k}_{v}');en[v]=m.new_bool_var(f't{k}_{v}');m.add(st[v]<=x[v]);m.add(en[v]<=x[v]);arcs.extend([(128,v,st[v]),(v,128,en[v])])
 m.add_circuit(arcs);m.add(sum(v*st[v] for v in N)<sum(v*en[v] for v in N));m.add(sum(x.values())>=49);m.add(sum(x.values())<=51)
 balance=sum((1 if v.bit_count()%2==0 else -1)*x[v] for v in N);m.add(balance>=-1);m.add(balance<=1)
 for v in N:
  for i in range(7):
   for j in range(i+1,7):
    sq=[v,v^(1<<i),v^(1<<j),v^(1<<i)^(1<<j)]
    if v==min(sq):m.add(sum(x[z] for z in sq)<=3);squares+=1
 for v in N:m.add_hint(x[v],int(v in seeds[k]))
 xs.append(x);starts.append(st);ends.append(en);directions.append(di);omissions.append(51-sum(x[v] for v in seeds[k]))
for v in N:m.add(xs[0][v]+xs[1][v]<=1)
m.add(sum(sum(x.values()) for x in xs)==100);m.add(sum(omissions)<=a.omissions)
# Applying h and swapping the paths exchanges their seed omission counts.
m.add(omissions[0]<=omissions[1])
modelpath=H/'data'/(a.tag+'.pbtxt');m.export_to_file(str(modelpath))
s=cp_model.CpSolver();s.parameters.num_search_workers=1;s.parameters.max_time_in_seconds=a.seconds;s.parameters.max_memory_in_mb=256
samples=[];stop=[];done=threading.Event()
def monitor():
 while not done.wait(1):
  snap=snapshot();samples.append(snap)
  if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:stop.append('RESOURCE_LIMIT');s.stop_search();return
t=threading.Thread(target=monitor,daemon=True);t.start();start=time.monotonic();code=s.solve(m);done.set();t.join();witness=None
if code in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
 paths=[]
 for k in range(2):
  q=[v for v in N if s.value(starts[k][v])];assert len(q)==1
  while not s.value(ends[k][q[-1]]):
   opts=[v for v in N[q[-1]] if s.value(directions[k][q[-1],v])];assert len(opts)==1;q.append(opts[0]);assert len(q)<=51
  assert len(q)==sum(s.value(xs[k][v]) for v in N) and len(set(q))==len(q)
  assert all(((u^q[j]).bit_count()==1)==(j==i+1) for i,u in enumerate(q) for j in range(i+1,len(q)))
  paths.append(q)
 assert sum(map(len,paths))==100 and not set(paths[0]).intersection(paths[1])
 lifted=[paths[0],[v+128 for v in paths[1]]];assert all((u^v).bit_count()!=1 for u in lifted[0] for v in lifted[1])
 witness=dict(projected_paths=paths,paths=lifted,fixed_face_vertices=100,omitted=[sorted(set(seeds[k])-set(paths[k])) for k in range(2)],added=[sorted(set(paths[k])-set(seeds[k])) for k in range(2)])
out=dict(status=stop[0] if stop else s.status_name(code),seconds=time.monotonic()-start,arguments=vars(a),case=c,seeds=seeds,shared_vertices=sorted(set(seeds[0])&set(seeds[1])),branches=s.num_branches,conflicts=s.num_conflicts,witness=witness,source_sha256=hashlib.sha256(raw).hexdigest(),placement_sha256=hashlib.sha256(placement.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),model_sha256=hashlib.sha256(modelpath.read_bytes()).hexdigest(),resource_gate=gate,resource_samples=samples,scope='Two independently variable, vertex-disjoint induced Q7 paths with total100 vertices, each49 to51 vertices. Total omissions from the two fixed minimum-overlap51-vertex seeds are capped. Their mutual symmetry is not required. Omission-order reduction uses the checked-in-script involution exchanging seeds. Native solver result, no Lean contradiction certificate.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','seconds','branches','conflicts']}),flush=True)
