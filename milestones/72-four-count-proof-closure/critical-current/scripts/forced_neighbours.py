"""Test the direct forced-zero argument independently of any SAT encoder."""
from pathlib import Path
from itertools import combinations
import json
HERE=Path(__file__).resolve().parents[1]
shapes=json.loads((HERE/'data/all-six-direction-shapes.json').read_text())['up_to_reversal']
nb=lambda v:{v^(1<<a) for a in range(9)}
rows=[]
for ds in shapes:
 w=[0]
 for d in ds:w.append(w[-1]^(1<<d))
 U=set().union(*(nb(w[i])-{w[i-1],w[i+1]} for i in range(1,6)))
 assert not(U&set(w))
 shares=[]
 for c in w[1:-1]:
  total=0
  for q in nb(c):
   e=sum({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=U for a,b in combinations(range(9),2))
   d=9-len(nb(q)&U);assert d>=1
   total+=12*e//d
  shares.append(total)
 rows.append(dict(directions=ds,forced_zero_vertices=len(U),share_lower=shares,total=sum(shares)))
assert all(r['total']==0 for r in rows)
(HERE/'data/forced-neighbours.json').write_text(json.dumps(dict(status='PASS_ZERO_DIRECT_LOWER_BOUND',rows=rows,scope='Direct forced-unselected-neighbour argument yields zero for every shape. This does not refute a stronger theorem using further snake constraints.'),indent=2)+'\n')
print('All nine direct forced-zero share bounds equal zero.')
