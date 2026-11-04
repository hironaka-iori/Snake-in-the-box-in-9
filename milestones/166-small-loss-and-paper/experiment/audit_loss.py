"""Exact, bounded Q9 loss audit; no search solver or proof-assistant claim."""
from pathlib import Path
from collections import Counter
from itertools import combinations
import json,hashlib,time
H=Path(__file__).resolve().parent;R=H.parents[2]
start=time.monotonic();pins={}
def load(rel):
 p=R/rel;pins[rel]=hashlib.sha256(p.read_bytes()).hexdigest();return json.loads(p.read_text())
faces=[(a,b) for a,b in combinations(range(9),2)]
def audit(vertices,path=None):
 S=set(vertices);assert len(S)==len(vertices) and all(0<=x<512 for x in S)
 d=[sum((q^(1<<a)) in S for a in range(9)) for q in range(512)]
 e=[0]*512;empty_squares=0
 for q in range(512):
  for a,b in faces:
   if q&(1<<a) or q&(1<<b):continue
   square=[q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)]
   if S.isdisjoint(square):
    empty_squares+=1
    for x in square:e[x]+=1
 loss=[12*e[q]%d[q] if d[q] else 12*e[q] for q in range(512)]
 parts=[12*sum(e[q] for q in range(512) if d[q]==0),sum((2*e[q])%5 for q in range(512) if d[q]==5),5*sum(e[q] for q in range(512) if d[q]==7)]
 assert all(e[q]<=(9-d[q])*(8-d[q])//2 if d[q]<=8 else e[q]==0 for q in range(512))
 assert sum(loss)==sum(parts)
 assert all(loss[q]==(12*e[q] if d[q]==0 else ((2*e[q])%5 if d[q]==5 else (5*e[q] if d[q]==7 else 0))) for q in range(512))
 shares=sum(sum(12*e[x^(1<<a)]//d[x^(1<<a)] for a in range(9)) for x in S)
 assert shares+sum(loss)==48*empty_squares
 components=[];unseen=set(S)
 while unseen:
  todo=[next(iter(unseen))];comp=[]
  while todo:
   x=todo.pop()
   if x not in unseen:continue
   unseen.remove(x);comp.append(x);todo.extend(x^(1<<a) for a in range(9) if x^(1<<a) in unseen)
  components.append(sorted(comp))
 if path is not None:
  assert path==vertices
  for i,x in enumerate(path):assert {x^(1<<a) for a in range(9)}&S==set(path[max(0,i-1):i]+path[i+1:i+2])
 is_path=len(components)==1 and ((len(S)==1 and d[next(iter(S))]==0) or (all(d[x] in [1,2] for x in S) and sum(d[x]==1 for x in S)==2))
 return dict(vertices=len(S),edges=sum(d[x] for x in S)//2,is_induced_path=is_path,path_order_checked=path is not None,selected_degree_histogram=dict(sorted(Counter(d[x] for x in S).items())),all_degree_histogram=dict(sorted(Counter(d).items())),component_sizes=sorted(map(len,components)),empty_squares=empty_squares,loss=sum(loss),loss_parts=dict(degree0=parts[0],degree5=parts[1],degree7=parts[2]),positive_loss_corners=[dict(q=q,d=d[q],e=e[q],loss=loss[q]) for q in range(512) if loss[q]],degree_empty_histogram=[dict(d=k[0],e=k[1],count=v) for k,v in sorted(Counter(zip(d,e)).items())])
control=load('outputs/snake9_witness.json')['vertex_sequence'];result=dict(control191=audit(control,control))
bank=load('work/bank9.json');rows=[]
for i,row in enumerate(bank):
 p=row['vertex_sequence'];a=audit(p,p);assert a['vertices']==192 and a['is_induced_path'];rows.append(dict(index=i,loss=a['loss'],parts=a['loss_parts']))
 assert time.monotonic()-start<60
result['bank191']=dict(count=len(rows),minimum=min(x['loss'] for x in rows),maximum=max(x['loss'] for x in rows),total=sum(x['loss'] for x in rows),rows=rows)
for n in [208,224]:
 j=load(f'milestones/11-local-ceiling/data/adversary{n}.json');a=audit(j['S']);assert a['selected_degree_histogram']=={2:n};result[f'adversary{n}']=a
# Elementary countermodels to dropping the path and size hypotheses.
for name,S in [('whole_cube',list(range(512))),('even_parity',[x for x in range(512) if x.bit_count()%2==0]),('single_square',[0,1,2,3])]:result[name]=audit(S)
# A rank-two parity check on seven coordinates; two coordinates are free.
columns=[1,1,2,2,3,3,3]
def syndrome(x):
 value=0
 for i,c in enumerate(columns):
  if x>>i&1:value^=c
 return value
code=[x for x in range(512) if syndrome(x)==0]
assert len(code)==128
for name,S in [('degree_two_zero_loss',code),('two_endpoints_zero_loss',[x for x in code if x!=0])]:
 a=audit(S);assert a['loss']==0;assert all(int(k) in [1,2,3] for k in a['all_degree_histogram']);a['selected_vertices']=S;result[name]=a
assert result['degree_two_zero_loss']['component_sizes']==[4]*32
assert result['two_endpoints_zero_loss']['component_sizes']==[3]+[4]*31
assert result['two_endpoints_zero_loss']['selected_degree_histogram']=={1:2,2:125}
# Break every square, selecting the removed corner via parity of bits 0,2,4.
forest=[x for x in code if ((x>>7)&3)!=(((x>>0)^(x>>2)^(x>>4))&1)]
a=audit(forest);assert len(forest)==96 and a['loss']==0 and a['component_sizes']==[3]*32
a['selected_vertices']=forest;result['acyclic_zero_loss']=a
columns4=[1,2,3,4,5,8,9,12,13]
def syndrome4(x):
 value=0
 for i,c in enumerate(columns4):
  if x>>i&1:value^=c
 return value
code4=[x for x in range(512) if syndrome4(x) in [0,1,2]]
a=audit(code4);assert len(code4)==96 and a['loss']==0 and a['selected_degree_histogram']=={2:96}
a['selected_vertices']=code4;result['rank_four_zero_loss']=a
result.update(status='PASS_EXACT_FINITE_LOSS_AUDIT',input_sha256=pins,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,new_Lean_theorem=False,universal_loss_lower_bound_proved=False,new_upper_bound=False)
(H/'results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:dict(vertices=v['vertices'],loss=v['loss'],components=dict(Counter(v['component_sizes'])),degree_histogram=v['all_degree_histogram']) for k,v in result.items() if isinstance(v,dict) and 'vertices' in v},indent=2))
