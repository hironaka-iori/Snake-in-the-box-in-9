from pathlib import Path
import sys,json,hashlib,itertools
H=Path(__file__).resolve().parent;sys.path[:0]=[str(H),str(H.parent/'pylibs')]
import numpy as np
from history_lift import Edge,lift_graph
from apply_npz_lift import transform
C=[Edge(i,i,(i+1)%4,[480,360,600,480][i]) for i in range(4)]
E=C+[Edge(4,0,2,900),Edge(5,1,0,700),Edge(6,1,1,800),Edge(7,2,4,700),Edge(8,4,2,900),Edge(9,3,0,1100),Edge(10,5,0,1200)]
a={'U':np.array([e.u for e in E],dtype=np.int64),'V':np.array([e.v for e in E],dtype=np.int64),'weight':np.array([e.weight for e in E],dtype=np.int64),'payload':np.arange(len(E),dtype=np.int32)*13}
meta={'states':6,'edges':len(E),'arrays_sha256':{k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}}
analysis={'cycle':[{'edge':e.id,'u':e.u,'v':e.v,'weight':e.weight} for e in C]}
out,projection,report=transform(a,meta,analysis,np)
S,LE,LP=lift_graph(E,{0,1,2,3});extra={(v,r):6+v*6+r-1 for v in range(4) for r in range(1,7)}
def idx(v,r):return v if r==0 else extra[v,r]
expected=sorted((idx(*S[e.u]),idx(*S[e.v]),e.weight,p) for e,p in zip(LE,LP))
actual=sorted((int(u),int(v),int(w),int(p)) for u,v,w,p in zip(out['U'],out['V'],out['weight'],projection))
assert actual==expected
assert np.array_equal(out['payload'],a['payload'][projection]);assert np.array_equal(projection[:len(E)],np.arange(len(E)))
raw={v:[] for v in range(6)};lifted={v:[] for v in range(30)}
for e in E:raw[e.u].append(e)
for j,(u,v,p) in enumerate(zip(out['U'],out['V'],projection)):lifted[int(u)].append((int(p),int(v)))
walks=0
# Independent explicit forbidden seven-ID pattern oracle, not membership counter.
patterns={tuple((phase+j)%4 for j in range(7)) for phase in range(4)}
def go(v,s,history,remaining):
 global walks
 forbidden=any(tuple(history[i:i+7]) in patterns for i in range(max(0,len(history)-6)))
 assert (s is None)==forbidden,(history,s)
 walks+=1
 if remaining:
  for e in raw[v]:
   nxt=[] if s is None else [t for p,t in lifted[s] if p==e.id]
   assert len(nxt)<=1
   go(e.v,nxt[0] if nxt else None,history+[e.id],remaining-1)
for v in raw:go(v,v,[],10)
neg=0
bad={k:v.copy() for k,v in a.items()};bad['weight'][0]+=1
try:transform(bad,meta,analysis,np)
except ValueError:neg+=1
else:raise AssertionError('tamper accepted')
bad_analysis=json.loads(json.dumps(analysis));bad_analysis['cycle'][0]['weight']+=1
try:transform(a,meta,bad_analysis,np)
except AssertionError:neg+=1
else:raise AssertionError('mismatched cycle accepted')
receipt={'status':'PASS','source_hashes':{n:hashlib.sha256((H/n).read_bytes()).hexdigest() for n in ['history_lift.py','apply_npz_lift.py']},'toy_source_nodes':6,'toy_source_edges':len(E),'lift_nodes':30,'lift_edges':len(projection),'exact_generic_NPZ_edge_multiset_equality':True,'extra_payload_projection_correct':True,'walks_against_explicit_7patterns':walks,'negative_controls':neg,'contains_parallel_unmarked_edge':True,'contains_unmarked_self_loop':True,'real_upstream_NPZ_loaded':False,'new_global_bound':None}
(H/'review_lift.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
