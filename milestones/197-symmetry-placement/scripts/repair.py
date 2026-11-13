"""Search the observed affine quotient using induced degrees and cycle cuts."""
from pathlib import Path
import argparse,hashlib,json,sys,threading,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--vertices',type=int,default=50);ap.add_argument('--omissions',type=int,default=4);ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--case',type=int,default=0);ap.add_argument('--free-ends',action='store_true');ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=H/'data/placements.json';raw=source.read_bytes();comparison=json.loads(raw);case=comparison['rows'][a.case]
profilepath=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';profile=json.loads(profilepath.read_bytes());seedpath=profile['7']['vertices']
def h(v):return sum(((v>>i)&1)<<case['permutation'][i] for i in range(7))^case['translation']
def g(v):return h(v&127)|((1-((v>>7)&1))<<7)
def orb(v):return min(v,g(v))
V=sorted({orb(v) for v in range(256)});N={v:sorted({orb(v^(1<<k)) for k in range(8)}) for v in V}
hint=[orb(v) for v in seedpath];root=hint[0]
assert len(V)==128 and len(set(hint))==51 and all(v not in N[v] for v in V)
assert all(g(g(v))==v and (v^g(v)).bit_count()>=2 for v in range(256))
assert all((((v^hint[j]).bit_count()==1)==(j==i+1)) for i,v in enumerate(hint) for j in range(i+1,len(hint)))
bad={tuple(sorted([v,orb(v^(1<<k))])) for v in V for k in range(8) if sum(orb(v^(1<<j))==orb(v^(1<<k)) for j in range(8))>1}
assert all(v.bit_count()%2==g(v).bit_count()%2 for v in V)
m=cp_model.CpModel();x={v:m.new_bool_var('x'+str(v)) for v in V};end={v:m.new_bool_var('end'+str(v)) for v in V};edge={}
for v in V:
 m.add(end[v]<=x[v])
 for w in N[v]:
  if v<w:
   y=m.new_bool_var('e'+str(v)+'_'+str(w));edge[v,w]=y;m.add(y<=x[v]);m.add(y<=x[w]);m.add(y>=x[v]+x[w]-1)
for v in V:m.add(sum(edge[min(v,w),max(v,w)] for w in N[v])==2*x[v]-end[v])
m.add(sum(x.values())==a.vertices);m.add(sum(end.values())==2)
if not a.free_ends:m.add(end[root]==1)
m.add(sum(x[v] for v in hint)>=len(hint)-a.omissions)
for v,w in bad:m.add(x[v]+x[w]<=1)
even=sum(x[v] for v in V if v.bit_count()%2==0);odd=sum(x[v] for v in V if v.bit_count()%2==1)
if a.vertices%2==0:m.add(even==odd)
else:m.add(even-odd>=-1);m.add(even-odd<=1)
squares=set()
for v in V:
 for w in N[v]:
  for z in N[w]:
   if z==v:continue
   for t in set(N[z])&set(N[v]):
    if t!=w:squares.add(tuple(sorted([v,w,z,t])))
for sq in squares:m.add(sum(x[v] for v in sq)<=3)
for v in V:m.add_hint(x[v],int(v in hint))
modelpath=H/'data'/(a.tag+'.pbtxt');assert not modelpath.exists();m.export_to_file(str(modelpath))
start=time.monotonic();iterations=[];cuts=[];samples=[];witness=None;terminal='TIME_LIMIT';stop=[]
while time.monotonic()-start<a.seconds:
 s=cp_model.CpSolver();s.parameters.num_search_workers=1;s.parameters.max_time_in_seconds=a.seconds-(time.monotonic()-start);s.parameters.max_memory_in_mb=256
 done=threading.Event()
 def monitor():
  while not done.wait(1):
   snap=snapshot();samples.append(snap)
   if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:stop.append('RESOURCE_LIMIT');s.stop_search();return
 worker=threading.Thread(target=monitor,daemon=True);worker.start();code=s.solve(m);done.set();worker.join()
 row=dict(status=s.status_name(code),seconds=s.wall_time,branches=s.num_branches,conflicts=s.num_conflicts,cuts_before=len(cuts));iterations.append(row)
 if code not in [cp_model.OPTIMAL,cp_model.FEASIBLE]:terminal=stop[0] if stop else row['status'];break
 selected={v for v in V if s.value(x[v])};unseen=set(selected);components=[]
 while unseen:
  comp={min(unseen)};todo=list(comp);unseen-=comp
  while todo:
   v=todo.pop()
   for w in N[v]:
    if w in selected and w not in comp:comp.add(w);unseen.remove(w);todo.append(w)
  components.append(comp)
 row['selected']=sorted(selected);row['components']=[sorted(c) for c in components]
 if len(components)>1:
  added=0
  for comp in components:
   if all(sum(w in selected for w in N[v])==2 for v in comp):
    assert all(sum(w in comp for w in N[v])==2 for v in comp)
    cycle=sorted(comp);m.add(sum(x[v] for v in cycle)<=len(cycle)-1);cuts.append(cycle);added+=1
  assert added==len(components)-1
  print(json.dumps(dict(iteration=len(iterations),cycles=added,elapsed=round(time.monotonic()-start,3))),flush=True)
  if stop:terminal=stop[0];break
  continue
 ends=[v for v in selected if sum(w in selected for w in N[v])==1];assert len(ends)==2
 path=[min(ends)]
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
 witness=dict(quotient_path=path,paths=[lift,partner],fixed_face_vertices=2*len(lift),omitted_orbits=sorted(set(hint)-selected));terminal='WITNESS';break
out=dict(status=terminal,arguments=vars(a),seconds=time.monotonic()-start,root=None if a.free_ends else root,affine_case=case,
 quotient_vertices=len(V),bad_edges=len(bad),squares=len(squares),iterations=iterations,dynamic_cycle_cuts=cuts,witness=witness,
 source_sha256=hashlib.sha256(raw).hexdigest(),profile_sha256=hashlib.sha256(profilepath.read_bytes()).hexdigest(),model_sha256=hashlib.sha256(modelpath.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 resource_gate=gate,resource_samples=samples,scope='Exact-size induced path in the specified Q7-plus-matching graph, with bounded omissions from the displayed51-vertex Q7 path and optional fixed endpoint. The seed has additional quotient contacts and is not itself a safe quotient path. Initial degree relaxation permits disjoint cycles; all recorded cycle cuts are required for the final model. Native solver exclusions are not Lean contradiction certificates.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status=terminal,seconds=out['seconds'],iterations=len(iterations),cuts=len(cuts),witness=bool(witness))),flush=True)
