from pathlib import Path
from collections import Counter
from itertools import combinations
import csv,random,sys,json
r=Path(__file__).resolve().parent
def valid(p):return len(set(p))==len(p) and all(0<=x<512 for x in p) and all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
def dump(f,paths):f.write_text(''.join(' '.join(map(str,p))+'\n' for p in paths))
if __name__=='__main__':
 rng=random.Random(825109);ws=Path.cwd();base=[list(map(int,z['vertices'].split())) for z in csv.DictReader(open('/tmp/q9_all190_20261119.csv'))];assert all(len(p)==191 and valid(p) for p in base)
 ref=[list(map(int,s.split())) for s in Path('/tmp/q9_core_191bank_m19.txt').read_text().splitlines()];ref=[p for p in ref if len(p)==192 and valid(p)]
 ctr=[];known=[];m=[x^((((x>>1)^(x>>6))&1)*66) ^ 24 for x in range(512)]
 for p in ref[:12]:
  q=[m[x] if any(a<=i<=b for a,b in ((4,18),(41,73),(105,130),(154,171))) else x for i,x in enumerate(p)]
  assert not valid(q);ctr.append(q);known.append(p)
 dump(r/'ctrl.pts',ctr);dump(r/'ctrl_truth.pts',known)
 pools=[[],[],[],[]];one=[list(map(int,l.split())) for l in (ws/'q9_fixed_bridge_onechord_walks.txt').read_text().splitlines()];pools[0]=one
 for i,p in enumerate(base):
  for _ in range(3):
   a,b=rng.sample(range(9),2);pools[1].append([p[0]^1<<a,*p,p[-1]^1<<b])
   a,b=rng.sample(range(9),2);v=p[-1]^1<<a;pools[2].append([*p,v,v^1<<b])
   cut=rng.randrange(190);axis=rng.choice([d for d in range(9) if 1<<d!=(p[cut]^p[cut+1])]);pools[3].append(p[:cut+1]+[p[cut]^1<<axis,p[cut+1]^1<<axis]+p[cut+1:])
 for i,p in enumerate(pools):dump(r/f'w{i}.pts',p)
 print('verified 190 parents',len(base),'191 controls',len(ctr),'walks',list(map(len,pools)))

