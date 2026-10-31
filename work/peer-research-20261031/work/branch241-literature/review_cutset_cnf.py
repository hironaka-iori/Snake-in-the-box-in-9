from pathlib import Path
from types import SimpleNamespace
import json
from cutset_cnf import build,add_cut
H=Path(__file__).parent;E,g,m,_=build([0,1,3,7,6],254)
size=len(E.cnf.clauses)
boundary=next(v for v in E.var if any(v^(1<<d) not in E.var for d in range(9)))
rejected=[]
for label,U,root,geo in [('incomplete_neighborhood',{boundary},boundary,g),('root_not_in_U',{1},0,g)]:
 try:add_cut(E,geo,m,U,root)
 except ValueError:rejected.append(label)
 else:raise AssertionError(label)
 assert len(E.cnf.clauses)==size
pairs=[(c,k) for c,k in zip(g.clauses,g.kinds) if not(k=='end_selected' and c[1]==g.var[1])]
fake=SimpleNamespace(var=g.var,clauses=[c for c,k in pairs],kinds=[k for c,k in pairs])
try:add_cut(E,fake,m,{1},1)
except ValueError:rejected.append('missing_endpoint_flag')
else:raise AssertionError('missing_endpoint_flag')
assert len(E.cnf.clauses)==size
out={'all_three_negative_guards_rejected_before_CNF_mutation':rejected,'boundary_vertex':boundary,'algebra':'sum(1-cross)+sum(1-end)+2root <= edges+|U| iff cross+end >=2root','review':'No valid-input soundness defect found; requires nontrivial global snake and genuine endpoint flags; not Lean-checked'}
(H/'cutset_cnf_independent_review.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
