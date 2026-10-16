import sys,json,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[3]/'Snake in the Box/work/solver_packages'))
from ortools.sat.python import cp_model
b=json.load(open('work/bank9.json'))
p=b[0]['vertex_sequence'][:112]
ban=set().union(*[{x}|{x^(1<<k) for k in range(9)} for x in p[:-1]])
h=p[-1]; r=set(); todo=[h]
while todo:
 v=todo.pop()
 for k in range(9):
  w=v^(1<<k)
  if w not in ban and w not in r:r.add(w);todo.append(w)
r.add(h)
m=cp_model.CpModel();x={v:m.new_bool_var(f'x{v}') for v in r};e={v:m.new_bool_var(f'e{v}') for v in r}
m.add(x[h]==1);m.add(e[h]==1);m.add(sum(e.values())==2)
for v in r:
 ns=[w for w in r if (v^w).bit_count()==1]
 m.add(e[v]<=x[v]);m.add(sum(x[w] for w in ns)==2-e[v]).only_enforce_if(x[v])
m.add(sum(x.values())>=82)
s=cp_model.CpSolver();s.parameters.max_time_in_seconds=60;s.parameters.num_search_workers=2
t=time.time();st=s.solve(m);print(len(r),s.status_name(st),time.time()-t,s.response_stats(),flush=True)
