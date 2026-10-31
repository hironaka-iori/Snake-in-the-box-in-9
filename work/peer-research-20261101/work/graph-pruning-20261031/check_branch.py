"""Independent numeric checker for an exhibited block-pruned branch.
Uses recursive articulation splitting, not the solver's Tarjan implementation.
"""
from pathlib import Path
import json
H=Path(__file__).resolve().parent

def components(V,n):
 V=set(V);out=[]
 while V:
  seed=min(V);V.remove(seed);todo=[seed];C={seed}
  while todo:
   v=todo.pop()
   for d in range(n):
    w=v^(1<<d)
    if w in V:V.remove(w);C.add(w);todo.append(w)
  out.append(C)
 return out

def split_blocks(V,n):
 for v in sorted(V):
  cs=components(V-{v},n)
  if len(cs)>1:return [b for c in cs for b in split_blocks(c|{v},n)]
 return [V]

def check(filename):
 d=json.loads(Path(filename).read_text());w=d['first_block_prune'];p=w['path'];n=d['n'];h=p[-1]
 assert len(p)==len(set(p))
 for i,v in enumerate(p):
  for j in range(i):assert ((v^p[j]).bit_count()==1)==(i-j==1)
 banned=set(p[:-1])|{v^(1<<k) for v in p[:-1] for k in range(n)}
 available=(set(range(1<<n))-banned-set(p))|{h};R=next(c for c in components(available,n) if h in c)
 assert R==set(w['residual']);B=split_blocks(R,n)
 assert {frozenset(b) for b in B}=={frozenset(b) for b in w['decomposition']['blocks']}
 arts={v for v in R if sum(v in b for b in B)>1};best=1
 def walk(i,entry,seen,U,penalty):
  nonlocal best
  U=U|B[i];seen=seen|{i}
  cycle=len(B[i])>=4 and all(sum((v^(1<<k)) in B[i] for k in range(n))==2 for v in B[i]);penalty+=cycle
  same=sum(v.bit_count()%2==h.bit_count()%2 for v in U);bound=min(len(U)-penalty,2*same,2*(len(U)-same)+1);best=max(best,bound)
  for cut in B[i]&arts:
   if cut==entry:continue
   for j,b in enumerate(B):
    if j not in seen and cut in b:walk(j,cut,seen,U,penalty)
 for i,b in enumerate(B):
  if h in b:walk(i,h if h in arts else None,set(),{h},0)
 need=d['target_edges']+1-len(p)+1
 assert best==w['bounds']['block'] and best<need
 return {'status':'PASS','prefix_vertices':len(p),'residual_vertices':len(R),'blocks':len(B),'needed_suffix_vertices':need,'proved_suffix_upper_bound':best,'branch_total_edges_upper_bound':len(p)+best-2,'target_edges':d['target_edges'],'method':'independent recursive articulation splitting','scope':'this one branch only; no Lean or global upper bound'}
if __name__=='__main__':
 r=check(H/'global235_probe.json');(H/'independent_branch_check.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
