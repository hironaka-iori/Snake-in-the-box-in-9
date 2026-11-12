"""Complete a two-path face across exactly four crossings, using connectivity flow."""
from pathlib import Path
import argparse,hashlib,json,sys,threading,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
from ortools.sat.python import cp_model
ap=argparse.ArgumentParser();ap.add_argument('--case',choices=['lower','bank','symmetric','quotient'],default='bank');ap.add_argument('--index',type=int,default=0);ap.add_argument('--target',type=int,default=192);ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=H/'data'/('symmetric-lift.json' if a.case=='symmetric' else 'quotient50.json' if a.case=='quotient' else 'forest-profiles.json');raw=source.read_bytes();data=json.loads(raw)
hint=[]
if a.case=='lower':n=7;paths=data['comparisons']['8']['blocks'][1::2];hint=sum(data['comparisons']['8']['blocks'][::2],[])
elif a.case=='bank':n=8;paths=data['bank_forests'][a.index]['paths'];hint=sum(data['bank_forests'][a.index]['complement_paths'],[])
elif a.case=='symmetric':n=8;paths=data['paths']
else:n=8;paths=data['witness']['paths']
size=1<<n;A=set(sum(paths,[]));ports={p[k] for p in paths for k in [0,-1]};pairs=[tuple(sorted([p[0],p[-1]])) for p in paths]
N={v:[v^(1<<k) for k in range(n)] for v in range(size)}
assert len(ports)==4 and len(A)==sum(map(len,paths)) and len(paths)==2
assert all(sum(w in A for w in N[v])==(1 if v in ports else 2) for v in A)
assert all((u^v).bit_count()!=1 for u in ports for v in ports)
V=sorted(set(range(size))-A|ports);targetB=a.target+1-len(A)
m=cp_model.CpModel();x={v:m.new_bool_var('x'+str(v)) for v in V};end={v:m.new_bool_var('end'+str(v)) for v in V};edge={}
for v in V:
 m.add(end[v]<=x[v])
 if v in ports:m.add(x[v]==1)
 for w in N[v]:
  if w in x and v<w:
   y=m.new_bool_var('e'+str(v)+'_'+str(w));edge[v,w]=y;m.add(y<=x[v]);m.add(y<=x[w]);m.add(y>=x[v]+x[w]-1)
for v in V:m.add(sum(edge[min(v,w),max(v,w)] for w in N[v] if w in x)+int(v in ports)==2*x[v]-end[v])
m.add(sum(x.values())==targetB);m.add(sum(end.values())==2)
# Contract each fixed A path to an always-present edge between its ports.
contracted=dict(edge)
for pair in pairs:assert pair not in contracted;contracted[pair]=1
neighbours={v:[] for v in V};flow={}
for (v,w),present in contracted.items():
 neighbours[v].append(w);neighbours[w].append(v)
 for u,z in [(v,w),(w,v)]:
  f=m.new_int_var(0,targetB-1,'f'+str(u)+'_'+str(z));flow[u,z]=f;m.add(f<=(targetB-1)*present)
root=min(ports)
for v in V:m.add(sum(flow[w,v]-flow[v,w] for w in neighbours[v])==(1-targetB if v==root else x[v]))
ae=sum(v.bit_count()%2==0 for v in A);ao=len(A)-ae;be=sum(x[v] for v in V if v.bit_count()%2==0);bo=sum(x[v] for v in V if v.bit_count()%2==1)
if a.target%2:m.add(ae+bo==ao+be)
else:m.add(ae+bo-ao-be>=-1);m.add(ae+bo-ao-be<=1)
squarecuts=0
for v in V:
 for i in range(n):
  for j in range(i+1,n):
   sq=[v,v^(1<<i),v^(1<<j),v^(1<<i)^(1<<j)]
   if v==min(sq) and all(w in x for w in sq):m.add(sum(x[w] for w in sq)<=3);squarecuts+=1
assert hint
for v in V:m.add(x[v]==int(v in hint))
modelpath=H/'data'/(a.tag+'.pbtxt');m.export_to_file(str(modelpath))
s=cp_model.CpSolver();s.parameters.num_search_workers=1;s.parameters.max_time_in_seconds=a.seconds;s.parameters.max_memory_in_mb=256
samples=[];stop=[];done=threading.Event()
def monitor():
 while not done.wait(1):
  snap=snapshot();samples.append(snap)
  if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:stop.append('RESOURCE_LIMIT');s.stop_search();return
t=threading.Thread(target=monitor,daemon=True);t.start();start=time.monotonic();status=s.solve(m);done.set();t.join();witness=None
if status in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
 B={v for v in V if s.value(x[v])};selected=A|{size+v for v in B};adj={v:[v^(1<<k) for k in range(n+1) if v^(1<<k) in selected] for v in selected}
 ends=[v for v in selected if len(adj[v])==1];assert len(ends)==2 and all(1<=len(z)<=2 for z in adj.values());p=[min(ends)]
 while True:
  opts=[v for v in adj[p[-1]] if len(p)<2 or v!=p[-2]]
  if not opts:break
  assert len(opts)==1;p.append(opts[0]);assert len(p)<=len(selected)
 assert len(p)==a.target+1 and len(set(p))==len(p)
 assert all((((v^p[j]).bit_count()==1)==(j==i+1)) for i,v in enumerate(p) for j in range(i+1,len(p)))
 witness=dict(path=p,second_face=sorted(B))
out=dict(status=stop[0] if stop else s.status_name(status),seconds=time.monotonic()-start,arguments=vars(a),fixed_paths=paths,ports=sorted(ports),fixed_face_vertices=len(A),target_second_face_vertices=targetB,
 allowed_vertices=len(V),square_cuts=squarecuts,source_sha256=hashlib.sha256(raw).hexdigest(),model_sha256=hashlib.sha256(modelpath.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),resource_gate=gate,resource_samples=samples,witness=witness,
 branches=s.num_branches,conflicts=s.num_conflicts,scope='Fixed two nonadjacent induced paths in one face. Exactly four crossing ports, variable opposite-face forest including singleton components, connected by flow after contracting fixed paths. Opposite-face selection fixed to the existing witness for reconstruction. Native solver result, no Lean contradiction certificate.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status=out['status'],seconds=out['seconds'],fixed_face=len(A),target=a.target,witness=bool(witness))),flush=True)
