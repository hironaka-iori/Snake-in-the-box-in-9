from pathlib import Path
import sys,json,hashlib
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H.parent/'pylibs'));import numpy as np
from apply_npz_lift import transform
from history_lift import Edge,lift_graph
base=[Edge(i,i,(i+1)%4,w) for i,w in enumerate([480,360,600,480])]+[Edge(4,0,4,1200),Edge(5,4,0,1200),Edge(6,8,9,480),Edge(7,9,8,480)]
a={'U':np.array([e.u for e in base],dtype=np.int32),'V':np.array([e.v for e in base],dtype=np.int32),'weight':np.array([e.weight for e in base],dtype=np.int32),'direction':np.arange(8,dtype=np.uint8),'count_code':np.arange(8,dtype=np.int32),'history':np.zeros(8,dtype=np.uint8)}
meta={'states':10,'edges':8,'arrays_sha256':{k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}};analysis={'cycle':[{'edge':e.id,'u':e.u,'v':e.v,'weight':e.weight} for e in base[:4]]}
b,projection,report=transform(a,meta,analysis,np);ss,ee,pr=lift_graph(base,{0,1,2,3})
# Map dense generic lift states to the adapter's preserved-base IDs.
nodes=range(4);translate=lambda state:state[0] if state[1]==0 else 10+state[0]*6+state[1]-1
expected={(translate(ss[e.u]),translate(ss[e.v]),e.weight,pr[e.id]) for e in ee}
actual={(int(u),int(v),int(w),int(k)) for u,v,w,k in zip(b['U'],b['V'],b['weight'],projection)}
assert actual==expected
bad={k:v.copy() for k,v in a.items()};bad['weight'][0]+=1
try:transform(bad,meta,analysis,np)
except ValueError:tamper=True
else:raise AssertionError('tampered graph accepted')
r={'status':'PASS','test_graph_only':True,'lifted_edges':len(actual),'state_count':report['states'],'projected_edge_rows_equal_generic_implementation':True,'changed_input_hash_rejected':tamper,'real_4957613_edge_graph_run':False}
(H/'npz_adapter_validation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
