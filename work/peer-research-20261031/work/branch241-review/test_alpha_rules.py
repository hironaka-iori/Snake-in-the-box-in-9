from pathlib import Path
from itertools import product
from types import SimpleNamespace
import json
from alpha_rules_probe import rules
from pb_binary import BinaryCNF
C=BinaryCNF();xs=[[C.fresh() for _ in range(36)] for _ in range(3)]
E=SimpleNamespace(cnf=C,centres=[0,1,2],by_centre={i:[(l,21) for l in ls] for i,ls in enumerate(xs)})
clauses=rules(E);checked=0
for counts in product([0,1,2,3,4,5,6,7,35,36],repeat=3):
 a=C.witness({l:j<counts[i] for i,ls in enumerate(xs) for j,l in enumerate(ls)})
 got=all(any(a[abs(l)]==(l>0) for l in c) for c in clauses)
 expected=all(k>=1 for k in counts) and all((x!=1 or y>=4) and (y!=1 or x>=4) for x,y in zip(counts,counts[1:])) and counts!=(2,2,2)
 assert got==expected,(counts,got,expected);checked+=1
r={'canonical_count_controls':checked,'exact_project_rule_semantics':True,'scope':'encoding check only, no new upper bound'}
Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
