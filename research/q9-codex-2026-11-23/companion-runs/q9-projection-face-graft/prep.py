from pathlib import Path
from itertools import combinations
from random import Random
import gzip,csv,json
r=Path(__file__).resolve().parent; ws=Path('/Users/yichenzhan/Documents/ChatGPT/snake-in-the-box')
def verify(p):
 assert len(set(p))==len(p) and all(0<=x<512 for x in p)
 assert all(((x^p[j]).bit_count()==1)==(i+1==j) for i,x in enumerate(p) for j in range(i+1,len(p)))
def word(p):
 m={};return tuple(m.setdefault(x^y,len(m)) for x,y in zip(p,p[1:]))
def lift(p,d):
 def col(x):return (x&((1<<d)-1))+((x>>(d+1))<<d)
 q=[col(x) for x in p];m={};norm=[];v=0
 for i,x in enumerate(p):
  if i and q[i]!=q[i-1]:v^=1<<m.setdefault(q[i]^q[i-1],len(m))
  norm.append(v+256*((x^p[0])>>d&1))
 return norm
def main():
 parents={}
 for line in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt'):
  p=list(map(int,line.split()))
  if len(p)!=192:continue
  k=min(word(p),word(p[::-1]));parents.setdefault(k,p)
 n191=len(parents)
 for obj in csv.DictReader(open('/tmp/q9_all190_20261119.csv')):
  p=list(map(int,obj['vertices'].split()));k=min(word(p),word(p[::-1]));parents.setdefault(k,p)
 paths=list(parents.values())
 for p in paths:verify(p)
 seen=set();rows=[]
 for i,p in enumerate(paths):
  for ori,q in enumerate((p,p[::-1])):
   for d in range(9):
    h=lift(q,d);k=tuple(h)
    if k in seen:continue
    seen.add(k);rows.append((i,ori,d,h))
 with (r/'parents.pts').open('w') as f:
  for i,ori,d,p in rows:print(i,ori,d,*p,file=f)
 controls=[];rng=Random(3095)
 for i,p in enumerate(paths[:n191]):
  if len(controls)>=4:break
  for d in range(9):
   h=lift(p,d);A=h[rng.randrange(2,6):];B=h[:-rng.randrange(2,6)];C={v%256 for v in h};sa={v%256 for v in A};sb={v%256 for v in B}
   if sa==C or sb==C or sa==sb:continue
   for fixed in combinations(range(8),2+len(controls)):
    mask=sum(1<<j for j in fixed);pt=next(iter(C-sa))&mask
    combined={z for z in A if (z&mask)!=pt}|{z for z in B if (z&mask)==pt}
    if {z%256 for z in combined}==C:
     controls.append(dict(parent=i,dim=d,mask=mask,value=pt,A=A,B=B,goal=191,truth=h));break
   if len(controls) and controls[-1]['parent']==i:break
 (r/'controls.json').write_text(json.dumps(controls))
 print('191_parent_classes',n191,'all_parent_classes',len(paths),'projected_traversals',len(rows),'controls',len(controls))
if __name__=='__main__':main()

