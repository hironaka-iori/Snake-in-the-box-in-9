from pathlib import Path
import sys,json,hashlib
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
from history_lift import Edge,lift_graph
C=[Edge(i,i,(i+1)%4,[480,360,600,480][i]) for i in range(4)]
E=C+[Edge(4,0,2,900),Edge(5,1,0,700),Edge(6,1,1,800),Edge(7,2,4,700),Edge(8,4,2,900),Edge(9,3,0,1100),Edge(10,5,0,1200)]
S,LE,LP=lift_graph(E,{0,1,2,3});raw={v:[] for v in range(6)};lifted={s:[] for s in range(len(S))}
for e in E:raw[e.u].append(e)
for e,p in zip(LE,LP):lifted[e.u].append((p,e.v));assert e.weight==E[p].weight and S[e.u][0]==E[p].u and S[e.v][0]==E[p].v
walks=0;patterns={tuple((phase+j)%4 for j in range(7)) for phase in range(4)}
def go(v,s,history,remaining):
 global walks
 forbidden=any(tuple(history[i:i+7]) in patterns for i in range(max(0,len(history)-6)))
 assert (s is None)==forbidden,(history,s);walks+=1
 if remaining:
  for e in raw[v]:
   nxt=[] if s is None else [t for p,t in lifted[s] if p==e.id]
   assert len(nxt)<=1
   go(e.v,nxt[0] if nxt else None,history+[e.id],remaining-1)
for v in raw:go(v,S.index((v,0)),[],10)
# Every source state and outgoing edge, including unreachable counter states, has exactly expected copies.
rows=0
for i,(v,r) in enumerate(S):
 for e in raw[v]:
  matches=[z for z,p in zip(LE,LP) if z.u==i and p==e.id]
  if e.id<4 and r==6:assert matches==[]
  else:
   assert len(matches)==1;assert S[matches[0].v]==(e.v,r+1 if e.id<4 else 0)
  rows+=1
out={'status':'PASS_STDLIB_AND_STATIC_REVIEW_ONLY','source_hashes':{n:hashlib.sha256((H/n).read_bytes()).hexdigest() for n in ['history_lift.py','apply_npz_lift.py']},'toy_nodes':6,'toy_edges':len(E),'lift_states':len(S),'lift_edges':len(LE),'walks_against_explicit_7patterns':walks,'all_state_outgoing_checks':rows,'parallel_unmarked_edge_and_unmarked_self_loop':True,'numpy_adapter_execution':'BLOCKED_BY_WINDOWS_APPLICATION_CONTROL','real_upstream_NPZ_loaded':False,'new_global_bound':None}
(H/'review_lift.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
