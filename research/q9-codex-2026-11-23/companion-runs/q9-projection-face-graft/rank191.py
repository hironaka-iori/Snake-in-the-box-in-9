from pathlib import Path
from collections import Counter
from time import monotonic
import json,sys,gzip
from run import r,ws,solve,verify,combine
from prep import word
def sh(p):return min(word(p),word(p[::-1]))
bank=[list(map(int,s.split())) for s in (r/'parents.pts').open()]
args=[[(list(map(int,s.split()))) for s in (r/n).open()] for n in ('grafts.pts','exact.pts')]
known={sh(q) for l in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt') if len(q:=list(map(int,l.split())))==192}
assert len(known)==131
seen=set();counts=Counter();winners={};start=monotonic()
with (r/'rank191.jsonl').open('w',1) as out:
 for l in (r/'ranked.pts').open():
  cost,err,delta,g,idx,flip,sz=map(int,l.split());a,b,m,v,*_=args[g][idx];A=bank[a][3:];B=bank[b][3:];h=combine(A,B,m,v,bool(flip));S=frozenset(z%256 for z in h)
  if S in seen:continue
  seen.add(S);st,p=solve(h,191,4500);label=None
  if p:
   verify(p);assert len(p)==192 and {z%256 for z in p}==S;key=sh(p);label='known' if key in known else 'new';winners[key]=p
   if label=='new':
    extensions=[]
    for q in (p,p[::-1]):
     for d in range(9):
      nx=q[-1]^(1<<d)
      if nx not in q and all((y^nx).bit_count()>1 for y in q[:-1]): extensions.append(q+[nx])
    for q in extensions:verify(q)
    (r/'novel191.json').write_text(json.dumps({'witness':p,'extensions':extensions,'metadata':[g,idx]}))
  counts[st]+=1;print(json.dumps([g,idx,cost,st,label,p],separators=(',',':')),file=out)
  if label=='new' or len(seen)>=1800 or monotonic()-start>40:break
print(dict(counts),'classes',len(winners),'new',len(set(winners)-known))

