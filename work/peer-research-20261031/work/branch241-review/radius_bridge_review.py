import sys,json
from collections import Counter
from pathlib import Path
R=Path(__file__).resolve().parent;BASE=R.parent/'branch241-next';sys.path[:0]=[str(BASE),str(BASE/'encoding')]
from github_query import build,bank_witness,REPO
from charge_fast import Geometry,Charges
from independent_global_snake import validate
bank=json.loads((REPO/'work/bank9.json').read_text());S=bank[67]['vertex_sequence'];path=S[:3]
score=Charges(Geometry(9),S).cheap()['r6plus']['values'][path[1]];rows=[]
for radius in range(4,10):
 E,g,m,meta=build(path,score,radius=radius);a=bank_witness(E,g,m,S);assert E.cnf.satisfied(a)
 assert len(set(E.var.values()))==len(E.var);assert set(E.var)==set(g.var)
 rows.append({'radius':radius,'vertex_variables':len(E.var),'all_clauses_satisfied_by_known_snake':True})
assert validate(S,path)['edges']==len(S)-1
local=json.loads((R/'probes/k1_cap21_result.json').read_text());selected=local['selection'];E,g,m,meta=build(path,21,radius=9);a=bank_witness(E,g,m,selected)
violations=Counter(k for c,k in zip(g.clauses,g.kinds) if not any(a[abs(m[abs(l)])]==(l>0) for l in c))
assert violations
result={'known_snake_positive_controls':rows,'local_cap21_model_rejected_by_full_geometry':dict(violations),'full_Q9_geometry_claim':'No cycles, degree1..2 and at most two endpoints imply a single nontrivial induced path.'}
(R/'radius_bridge_results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
