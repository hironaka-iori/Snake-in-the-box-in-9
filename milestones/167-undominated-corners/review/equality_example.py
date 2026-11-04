"""Independent exact check of the degree-only equality example at e(0)=4."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import json,hashlib
H=Path(__file__).resolve().parent
matching=[(0,1),(2,3),(4,5),(6,7)]
missing={sum(1<<i for i in edge) for edge in matching}
S={sum(1<<i for i in pair) for pair in combinations(range(9),2)}-missing
S|={sum(1<<i for i in triple) for triple in combinations(range(9),3) if any(set(edge)<=set(triple) for edge in matching)}
d={x:sum(x^(1<<i) in S for i in range(9)) for x in range(512)}
e=sum(not S.intersection([0,1<<a,1<<b,(1<<a)|(1<<b)]) for a,b in combinations(range(9),2))
assert len(S)==60 and d[0]==0 and e==4
assert Counter(d[x] for x in S)=={1:8,2:52}
components=[];remaining=set(S)
while remaining:
 todo=[next(iter(remaining))];comp=[]
 while todo:
  x=todo.pop()
  if x not in remaining:continue
  remaining.remove(x);comp.append(x);todo.extend(x^(1<<i) for i in range(9) if x^(1<<i) in remaining)
 components.append(sorted(comp))
assert sorted(map(len,components))==[3]*4+[8]*6
# The eight forced endpoints are precisely the isolated direction joined to each matched direction.
assert {x for x in S if d[x]==1}=={(1<<8)|(1<<i) for i in range(8)}
result=dict(status='PASS_EXACT_DEGREE_ONLY_EQUALITY_EXAMPLE',selected_vertices=sorted(S),vertices=len(S),selected_degree_histogram=dict(sorted(Counter(d[x] for x in S).items())),component_sizes=sorted(map(len,components)),degree_at_zero=d[0],empty_squares_at_zero=e,is_snake=False,reason='Ten components, including six cycles, and eight endpoints.',script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),new_Lean_theorem=False)
(H/'equality-example.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='selected_vertices'},indent=2))
