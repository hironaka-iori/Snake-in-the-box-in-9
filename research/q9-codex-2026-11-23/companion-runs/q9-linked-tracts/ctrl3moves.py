from prep import *
from functools import lru_cache
OUT=[]
adj=[{x^(1<<d) for d in range(9)} for x in range(512)]
def moves(p):
 found=[]
 for stride in (5,7,9,6,8):
  for i in range(7,len(p)-7-stride):
   j=i+stride;core=set(p[:i+1]+p[j:]);u,t=p[i],p[j]
   def go(cur,steps,seq,on):
    d=(cur^t).bit_count()
    if d>steps or (d-steps)%2:return
    if steps==1:
     if d==1 and seq!=p[i+1:j] and set(seq)!=set(p[i+1:j]):return seq
     return
    for x in adj[cur]:
     if x in on:continue
     if (adj[x]&on)!=( {cur,t} if steps==2 else {cur} ):continue
     a=go(x,steps-1,seq+[x],on|{x})
     if a is not None:return a
   for n in (stride-2,stride):
    a=go(u,n,[],core)
    if a is not None:
     q=p[:i+1]+a+p[j:]
     if ok(q):found.append((i,j,a));break
  if len(found)>25:break
 return found
def main():
 seen=set()
 for line in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt'):
  p=list(map(int,line.split()))
  if len(p)!=192 or shape(p) in seen:continue
  seen.add(shape(p));ops=moves(p)
  for triple in combinations(sorted(ops),3):
   if any(triple[z+1][0]-triple[z][1]<4 for z in (0,1)):continue
   a=p[:]
   for i,j,body in triple[::-1]:a[i+1:j]=body
   if not ok(a):continue
   OUT.append((a,p[2:-2],triple));break
  if len(OUT)>=3:break
 dump(r/'ctrl3.pts',[p for a,b,_ in OUT for p in (a,b)]);print('checked_sources',len(seen),'controls',len(OUT),'intervals',[[tuple(q[:2]) for q in m] for _,_,m in OUT])
if __name__=='__main__':main()

