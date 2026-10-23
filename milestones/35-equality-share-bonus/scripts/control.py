"""Check the tagged encoder on the complete 138-edge positive control."""
import json
from pathlib import Path
from tagged_pair import TaggedPairShare,Cadical153
from pair_model import census
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
w=json.loads((ROOT/'milestones/34-distance-three-sharpness/data/witness-1.json').read_text())
e=TaggedPairShare(w['dirs'],[(0,21)]*6,42)
s=set(w['vertex_sequence'])&set(e.ball)
with Cadical153(bootstrap_with=e.clauses) as solver:
 assert solver.solve(assumptions=[i if v in s else -i for v,i in e.var.items()])
c=census(s,9,e.window[1:-1]);c.pop('degree')
assert c['alpha'][0]+c['alpha'][5]==9
assert [c['share'][j] for j in (0,5)]==[25,17]
r=dict(status='SAT',fixed_witness_edges=w['edges'],ball_vertices=len(e.ball),pair_counts=[c['alpha'][j] for j in (0,5)],pair_shares=[25,17],cap=42)
(HERE/'data/tagged-control.json').write_text(json.dumps(r,indent=2)+'\n')
print(r)
