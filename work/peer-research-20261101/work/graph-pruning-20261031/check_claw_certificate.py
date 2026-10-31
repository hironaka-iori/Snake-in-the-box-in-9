"""Check a disjoint packing certificate without calling any solver bound function."""
from pathlib import Path
import json
H=Path(__file__).resolve().parent;d=json.loads((H/'claw_witness.json').read_text());P=d['prefix'];R=set(d['residual']);h=P[-1];seen=set();loss=0
for group in d['groups']:
 V=set(group['vertices']);assert len(V)==len(group['vertices']) and V<=R and not V&seen;seen|=V
 if group['kind']=='endpoint_star':
  N={v for v in R if (v^h).bit_count()==1};assert V==N|{h};assert group['loss']==max(0,len(N)-1)
 elif group['kind']=='claw':
  v=group['center'];assert len(V)==4 and v in V and all((v^w).bit_count()==1 for w in V-{v});assert group['loss']==1
 else:raise AssertionError('unknown group')
 loss+=group['loss']
assert len(R)-loss==d['upper_bound']
r={'status':'PASS','residual_vertices':len(R),'disjoint_groups':len(d['groups']),'forced_omissions':loss,'suffix_vertices_upper_bound':d['upper_bound'],'branch_edges_upper_bound':len(P)+d['upper_bound']-2,'scope':'same one branch, not global; residual validity separately checked by check_branch.py'}
(H/'independent_claw_check.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
