"""Untrusted degree-relaxation probe; no geometric Lean certificate is claimed."""
from itertools import combinations
from pathlib import Path
import json
bank=json.loads(Path('work/bank9.json').read_text())
p=bank[0]['vertex_sequence'][:112]
ban=set().union(*[{v}|{v^(1<<k) for k in range(9)} for v in p[:-1]])
h=p[-1];r=set();todo=[h]
while todo:
    v=todo.pop()
    for k in range(9):
        w=v^(1<<k)
        if w not in ban and w not in r:r.add(w);todo.append(w)
r.add(h);r=sorted(r)
variables={v:i+1 for i,v in enumerate(r)};next_id=len(r)+1;clauses=[];ends=[]
def new():
    global next_id
    v=next_id;next_id+=1;return v
for v in r:
    x=variables[v];ns=[variables[w] for w in r if (v^w).bit_count()==1]
    e=new();ends.append((v,e))
    clauses.extend([[-e,x],[-x]+ns])
    for a,b,c in combinations(ns,3):clauses.append([-x,-a,-b,-c])
    for a,b in combinations(ns,2):clauses.append([-e,-a,-b])
    for a in ns:clauses.append([-x,e]+[b for b in ns if a!=b])
    if v==h:clauses.extend([[x],[e]])
for (v,e),(w,f) in combinations(ends,2):
    if v!=h and w!=h:clauses.append([-e,-f])
# At most len(r)-82 excluded vertices. Sinz forward sequential counter.
k=len(r)-82
prev=[]
for i,v in enumerate(r):
    lit=-variables[v];cur=[new() for _ in range(k)]
    clauses.append([-lit,cur[0]])
    if prev:
        for j in range(k):clauses.append([-prev[j],cur[j]])
        for j in range(1,k):clauses.append([-lit,-prev[j-1],cur[j]])
        clauses.append([-lit,-prev[-1]])
    prev=cur
out=Path('work/lean/degree112.cnf')
out.write_text(f'p cnf {next_id-1} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
out.with_suffix('.json').write_text(json.dumps({'clauses':clauses,'reasons':[None]*len(clauses),'variables':next_id-1}))
print(len(r),next_id-1,len(clauses),flush=True)
