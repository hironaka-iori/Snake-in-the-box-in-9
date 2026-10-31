from pathlib import Path
import json
from independent_encoding_review import Geometry,direct
from charge_fast import Charges
H=Path(__file__).resolve().parent;R=H.parent/'branch241-audit/repo/milestones/11-local-ceiling/data';G=Geometry(9);rows=[]
for name in ['adversary208','adversary224']:
 d=json.loads((R/(name+'.json')).read_text());S=set(d['S']);C=Charges(G,S);q=C.cheap()['r6plus']['values'];candidates=[];violations=[]
 for cycle in d['cycles']:
  n=len(cycle)
  for i,x in enumerate(cycle):
   assert (x^cycle[(i+1)%n]).bit_count()==1
   triple=[cycle[(i+j)%n] for j in range(3)];candidates.append((sum(q[v] for v in triple),triple))
   y=cycle[(i+1)%n]
   if C.alpha[x]<1 or C.alpha[x]==1 and C.alpha[y]<4 or C.alpha[y]==1 and C.alpha[x]<4 or all(C.alpha[v]==2 for v in triple):violations.append(triple)
 score,window=min(candidates);ind=[]
 for v in window:
  a,b,c,e,_=direct(G,S,v);ind.append(21*a+2*b+c+e)
 assert sum(ind)==score
 rows.append({'name':name,'vertices':len(S),'cycle_lengths':list(map(len,d['cycles'])),'minimum_three_centre_score':score,'minimizing_centres':window,'independent_set_enumeration_scores':ind,'new_alpha_rule_violations':len(violations),'scope':'cycle union only; not a snake, not a universal bound'})
out={'results':rows,'finding':'These two known cycle unions do not by themselves refute the proposed triple-score threshold255. This does not exclude other cycle-union obstructions.'};H.joinpath('adversary_score_followup.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
