"""Elementary forced-edge contradictions in the augmented Hamiltonian graph."""
from pathlib import Path
import hashlib,json,time
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=H/'data/candidates.json';raw=json.loads(source.read_bytes());out=[];started=time.monotonic()
for b in raw['bases']:
 U=set(b['vertices']);adj={v:set() for v in U|{512}};portset=set()
 for z in range(512):
  ns=U&{z^(1<<j) for j in range(9)}
  if len(ns)==1:portset|=ns
  elif len(ns)==2:v,w=sorted(ns);adj[v].add(w);adj[w].add(v)
 for v in portset:adj[v].add(512);adj[512].add(v)
 F={v:set() for v in adj};trace=[];reason=None;changed=True
 while changed and reason is None:
  changed=False
  for v in sorted(adj):
   if len(adj[v])<2:reason=dict(kind='DEGREE_BELOW_TWO',vertex=v);break
   if len(F[v])>2:reason=dict(kind='FORCED_DEGREE_ABOVE_TWO',vertex=v);break
   if len(adj[v])==2:
    for w in sorted(adj[v]-F[v]):F[v].add(w);F[w].add(v);trace.append(['force',v,w]);changed=True
   if len(F[v])==2:
    for w in sorted(adj[v]-F[v]):
     assert v not in F[w]
     adj[v].remove(w);adj[w].remove(v);trace.append(['delete',v,w]);changed=True
  if reason:break
  unseen=set(adj)
  while unseen:
   todo=[min(unseen)];C=set()
   while todo:
    v=todo.pop()
    if v in C:continue
    C.add(v);unseen.discard(v);todo.extend(F[v]-C)
   if len(C)<len(adj) and all(len(F[v])==2 for v in C):reason=dict(kind='PROPER_FORCED_CYCLE',vertices=sorted(C));break
 if reason is None:
  for v in sorted(adj):
   left=set(adj)-{v};components=[]
   while left:
    todo=[min(left)];C=set()
    while todo:
     w=todo.pop()
     if w in C:continue
     C.add(w);left.discard(w);todo.extend((adj[w]&left)-C)
    components.append(sorted(C))
   if len(components)>1:reason=dict(kind='ARTICULATION',vertex=v,components=components);break
 out.append(dict(id=b['id'],trace=trace,contradiction=reason,status='CERTIFICATE' if reason else 'UNRESOLVED'))
dest=H/'data/forced-cycles.json';assert not dest.exists()
result=dict(status='COMPLETE_PROPAGATION',rows=out,certified=sum(r['status']=='CERTIFICATE' for r in out),total=len(out),seconds=time.monotonic()-started,source_sha256=sha(source),script_sha256=sha(__file__),scope='Every spanning cycle uses both available edges at a degree-two vertex. Two forced edges exclude all other incident edges. Degree below two, forced degree above two, a proper forced cycle, or an articulation point contradicts a spanning cycle. Finite traces require independent replay; not Lean certificates.')
dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print('FORCED_CERTIFICATES',result['certified'],'of',len(out),'seconds',result['seconds'])
