import json,sys,random
from pathlib import Path
from cheap_folded import FixedPathObjective
from cheap_objective import CheapObjective
from charge_fast import Geometry,Charges
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[1]/'branch241-audit/repo';G=Geometry(9);bank=json.loads((REPO/'work/bank9.json').read_text());path=bank[67]['vertex_sequence'];rng=random.Random(241)
rows=[]
for k in (1,3,7,9):
 E=FixedPathObjective(G,path[:k+2]);B=CheapObjective(G,path[1:k+1]);tests=0
 for i in range(64):
  S=E.selected|{v for v in E.ball-E.selected-E.forbidden if rng.random()<.25}
  assert E.evaluate(S)==B.evaluate(S);tests+=1
 P=FixedPathObjective(G,path[:k+2],occupancy_bonus=True);want=Charges(G,path).cheap()['r6plus']['values'];got=P.evaluate(path)
 assert got=={x:want[x] for x in P.centres}
 rows.append({'centres':k,'random_CNF_equivalence_assignments':tests,'bonus_variables':P.cnf.nv,'bonus_clauses':len(P.cnf.clauses),'bonus_terms':len(P.terms),'bonus_offset':P.offset,'bonus_exact_score':sum(got.values())})
 if k==9:(HERE/'cheap_bonus_bank67.json').write_text(json.dumps(P.export()))
(HERE/'folding_and_bonus_checks.json').write_text(json.dumps({'all_passed':True,'controls':rows},indent=2));print(json.dumps(rows,indent=2))
