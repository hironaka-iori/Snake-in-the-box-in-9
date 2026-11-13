"""Connected induced quotient paths for the row4147 symmetry."""
from pathlib import Path
import argparse,hashlib,json,sys,threading,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--vertices',type=int,default=50);ap.add_argument('--omissions',type=int,default=5);ap.add_argument('--branch',type=int,default=-1);ap.add_argument('--root',type=int,default=-1);ap.add_argument('--seconds',type=float,default=60);ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=H/'data/structure.json';raw=source.read_bytes();d=json.loads(raw);case=d['case'];seed=d['seed']
def h(v):return sum(((v>>i)&1)<<case['permutation'][i] for i in range(7))^case['translation']
def g(v):return h(v&127)|((1-((v>>7)&1))<<7)
def orb(v):return min(v,g(v))
N={v:sorted(set([v^(1<<k) for k in range(7)]+[h(v)])) for v in range(128)}
assert all(len(N[v])==8 and v not in N[v] for v in N)
m=cp_model.CpModel();x={v:m.new_bool_var('x'+str(v)) for v in N};arcs=[];directions={}
for v in N:arcs.append((v,v,x[v].Not()))
for v in N:
 for w in N[v]:
  if v<w:
   f=m.new_bool_var('a'+str(v)+'_'+str(w));b=m.new_bool_var('a'+str(w)+'_'+str(v))
   arcs.extend([(v,w,f),(w,v,b)]);directions[v,w]=f;directions[w,v]=b
   m.add(f+b<=x[v]);m.add(f+b<=x[w]);m.add(f+b>=x[v]+x[w]-1)
starts={};ends={}
for v in N:
 starts[v]=m.new_bool_var('s'+str(v));ends[v]=m.new_bool_var('t'+str(v))
 m.add(starts[v]<=x[v]);m.add(ends[v]<=x[v]);arcs.extend([(128,v,starts[v]),(v,128,ends[v])])
m.add_circuit(arcs);m.add(sum(x.values())==a.vertices)
if a.root>=0:m.add(starts[a.root]==1)
else:m.add(sum(v*starts[v] for v in N)<sum(v*ends[v] for v in N))
if a.omissions>=0:m.add(sum(x[v] for v in seed)>=51-a.omissions)
if 0<=a.branch<4:
 m.add(x[seed[4]]==1);m.add(x[seed[38]]==1)
 m.add(x[seed[[3,5][a.branch//2]]]==0);m.add(x[seed[[37,39][a.branch%2]]]==0)
elif a.branch==4:m.add(x[seed[4]]==0)
elif a.branch==5:m.add(x[seed[38]]==0)
else:assert a.branch==-1
for c in d['cliques']:m.add(sum(x[v] for v in c)<=2)
squares=set()
for v in N:
 for w in N[v]:
  for z in N[w]:
   if z!=v:
    for t in set(N[z])&set(N[v]):
     if t!=w:squares.add(tuple(sorted([v,w,z,t])))
for sq in squares:m.add(sum(x[v] for v in sq)<=3)
if a.omissions>=0:
 for v in N:m.add_hint(x[v],int(v in seed))
modelpath=H/'data'/(a.tag+'.pbtxt');assert not modelpath.exists();m.export_to_file(str(modelpath))
s=cp_model.CpSolver();s.parameters.num_search_workers=1;s.parameters.max_time_in_seconds=a.seconds;s.parameters.max_memory_in_mb=256
samples=[];stop=[];done=threading.Event()
def monitor():
 while not done.wait(1):
  snap=snapshot();samples.append(snap)
  if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:stop.append('RESOURCE_LIMIT');s.stop_search();return
worker=threading.Thread(target=monitor,daemon=True);worker.start();start=time.monotonic();code=s.solve(m);done.set();worker.join();witness=None
if code in [cp_model.FEASIBLE,cp_model.OPTIMAL]:
 selected={v for v in N if s.value(x[v])};p=[v for v in N if s.value(starts[v])];assert len(p)==1
 while not s.value(ends[p[-1]]):
  opts=[v for v in N[p[-1]] if s.value(directions[p[-1],v])];assert len(opts)==1;p.append(opts[0]);assert len(p)<=a.vertices
 assert len(p)==a.vertices and set(p)==selected
 assert all((p[j] in N[v])==(j==i+1) for i,v in enumerate(p) for j in range(i+1,len(p)))
 lift=[p[0]]
 for z in p[1:]:
  opts=[lift[-1]^(1<<k) for k in range(8) if orb(lift[-1]^(1<<k))==z];assert len(opts)==1;lift.append(opts[0])
 partner=[g(v) for v in lift]
 assert len(set(lift+partner))==2*len(lift) and all((v^w).bit_count()!=1 for v in lift for w in partner)
 for q in [lift,partner]:assert all(((v^q[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(q) for j in range(i+1,len(q)))
 witness=dict(quotient_path=p,paths=[lift,partner],omitted_seed_vertices=sorted(set(seed)-selected),fixed_face_vertices=2*len(p))
out=dict(status=stop[0] if stop else s.status_name(code),arguments=vars(a),seconds=time.monotonic()-start,branches=s.num_branches,conflicts=s.num_conflicts,witness=witness,squares=len(squares),cliques=len(d['cliques']),source_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),model_sha256=hashlib.sha256(modelpath.read_bytes()).hexdigest(),resource_gate=gate,resource_samples=samples,scope='Connected induced path in the fixed row4147 quotient using a directed circuit through one dummy vertex. Exact target size, optional seed retention and endpoint/branch restrictions. Native solver result without Lean contradiction certificate.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','seconds','branches','conflicts']}),flush=True)
