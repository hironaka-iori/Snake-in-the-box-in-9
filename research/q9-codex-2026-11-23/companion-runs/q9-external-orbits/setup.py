from pathlib import Path
from itertools import combinations
from collections import Counter
from hashlib import sha256
import json
r=Path(__file__).resolve().parent
def flaws(p):
 return [(i,j) for i,j in combinations(range(len(p)),2) if ((p[i]^p[j]).bit_count()!=1 if j==i+1 else (p[i]^p[j]).bit_count()<2)]
def check(p,L):
 assert len(p)==L+1 and len(set(p))==len(p) and all(0<=v<512 for v in p) and not flaws(p)
def read(f):return [list(map(int,s.split())) for s in f.read_text().splitlines()]
def dump(f,ps):f.write_text(''.join(' '.join(map(str,x))+'\n' for x in ps))
def main():
 inp=Path.cwd()/'q9_port_external_onechord.txt';P=read(inp);assert len(P)==36
 defects=[]
 for p in P:
  assert len(p)==193 and len(set(p))==193 and all(0<=x<512 for x in p) and all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
  q=flaws(p);assert len(q)==1;defects.extend(q)
 dump(r/'walks.pts',P);truth=read(Path('/tmp/q9_core_191bank_m19.txt'))[:4]
 def tr(x,a,b):
  y=x^37
  return ((y^((1<<a|1<<b) if (y>>a^y>>b)&1 else 0))^37)
 Q=[]
 for p in truth:
  check(p,191);q=p[:]
  for i,x in enumerate(p):
   if 7<=i<25 or 122<=i<138:q[i]=tr(x,0,2)
   elif 49<=i<73 or 161<=i<177:q[i]=tr(x,2,5)
   elif 87<=i<100:q[i]=tr(tr(x,0,2),2,5)
  assert flaws(q);Q.append(q)
 dump(r/'controls.pts',Q);dump(r/'truth.pts',truth)
 print('source',sha256(inp.read_bytes()).hexdigest(),'defects',dict(Counter(defects)))
if __name__=='__main__':main()

