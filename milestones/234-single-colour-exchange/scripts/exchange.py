"""Exact static cover of one-exchange minority classes; no solver invoked."""
from pathlib import Path
import argparse,collections,hashlib,json,time
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def bits(mask):
 while mask:
  b=mask&-mask;yield b.bit_length()-1;mask-=b
ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--start-core',type=int,default=0);a=ap.parse_args()
source=H/'data/bases.json';raw=json.loads(source.read_bytes());assert all(sha(p)==h for p,h in raw['pins'].items())
target=H/'data'/(a.tag+'.json');assert not target.exists()
N=[sum(1<<(x^(1<<j)) for j in range(9)) for x in range(512)]
labels_by_parity=[[v for v in range(512) if v.bit_count()%2==p] for p in [0,1]]
out=dict(status='RUNNING',arguments=vars(a),source_sha256=sha(source),script_sha256=sha(__file__),cores=[],candidates=[],code_names=['CANDIDATE','ISOLATED','FEWER_THAN_TWO_PORTS','TOO_MANY_LEAVES','UNSUPPORTED_LEAF','DISCONNECTED'],scope='Every removed original vertex and every outside same-parity insertion. Static exact contraction obstructions only. Candidate means unresolved Hamiltonian query. Repeated resulting classes retain separate descriptions; no distinct-class count is claimed.')
started=time.monotonic();count=collections.Counter();core_id=-1
def save():target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();decisionpath=H/'data'/(a.tag+'-decisions.bin');assert not decisionpath.exists()
with decisionpath.open('wb') as decisions:
 for base in raw['bases']:
  U=sorted(base['vertices']);assert len(U)==len(set(U))==96
  parity=U[0].bit_count()%2;assert all(v.bit_count()%2==parity for v in U)
  umask=sum(1<<v for v in U);adds=[v for v in labels_by_parity[parity] if not (umask>>v)&1];assert len(adds)==160
  opposite=labels_by_parity[1-parity]
  for removed in U:
   core_id+=1
   if core_id<a.start_core:continue
   if time.monotonic()-started>=a.seconds:break
   C=[v for v in U if v!=removed];mask=umask^(1<<removed);adj={v:0 for v in C};portlabels={};edge_labels={}
   ns={z:N[z]&mask for z in opposite}
   for z,t in ns.items():
    k=t.bit_count()
    if k==1:v=t.bit_length()-1;portlabels[v]=portlabels.get(v,0)|(1<<z)
    elif k==2:
     v,w=bits(t);adj[v]|=1<<w;adj[w]|=1<<v;edge_labels[t]=edge_labels.get(t,0)|(1<<z)
   core_ports=sum(1<<v for v in portlabels);local=collections.Counter();codes=bytearray()
   for ai,added in enumerate(adds):
    ident=core_id*160+ai;nm=N[added];newadj=0;newport=False;ports=core_ports;changed={}
    def current(v):return changed.get(v,adj[v])
    for z in bits(nm):
     t=ns[z];k=t.bit_count()
     if k==0:newport=True
     elif k==1:
      v=t.bit_length()-1;newadj|=t;changed[v]=current(v)|(1<<added)
      if not (portlabels[v]&~nm):ports&=~(1<<v)
     elif k==2 and not (edge_labels[t]&~nm):
      v,w=bits(t);changed[v]=current(v)&~(1<<w);changed[w]=current(w)&~(1<<v)
    if newport:ports|=1<<added
    degrees=[(v,current(v).bit_count()) for v in C]+[(added,newadj.bit_count())]
    isolated=next((v for v,k in degrees if k==0),None)
    leaves=[v for v,k in degrees if k==1]
    if isolated is not None:code=1
    elif ports.bit_count()<2:code=2
    elif len(leaves)>2:code=3
    elif any(not (ports>>v)&1 for v in leaves):code=4
    else:
     selected=mask|(1<<added);reached=0;todo=selected&-selected
     while todo:
      b=todo&-todo;todo-=b;v=b.bit_length()-1
      if reached&b:continue
      reached|=b;neigh=newadj if v==added else current(v);todo|=neigh&~reached
     if reached!=selected:code=5
     else:
      code=0;out['candidates'].append(dict(id=ident,base=base['id'],removed=removed,added=added))
    codes.append(code);local[code]+=1;count[code]+=1
   decisions.write(codes);decisions.flush()
   out['cores'].append(dict(core=core_id,base=base['id'],removed=removed,statuses=dict(local)))
   out['next_core']=core_id+1;out['descriptions']=sum(count.values());out['statuses']={out['code_names'][k]:v for k,v in count.items()}
   if core_id%96==95:save();print(json.dumps(dict(next_core=core_id+1,statuses=out['statuses'],seconds=time.monotonic()-started)),flush=True)
  else:continue
  break
out['status']='COMPLETE_STATIC_COVER' if out.get('next_core')==13920 else 'TIME_LIMIT'
out['seconds']=time.monotonic()-started;out['decisions_sha256']=sha(decisionpath);out['decision_bytes']=decisionpath.stat().st_size;save()
print(json.dumps(dict(status=out['status'],next_core=out.get('next_core'),descriptions=out.get('descriptions'),statuses=out.get('statuses'),seconds=out['seconds'])),flush=True)
