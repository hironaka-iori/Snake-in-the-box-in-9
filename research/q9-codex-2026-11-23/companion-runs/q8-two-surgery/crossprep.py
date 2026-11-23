from pathlib import Path
from collections import defaultdict
import random
from verify import parse
r=Path(__file__).resolve().parent;bank=defaultdict(dict)
def norm(p):
 m={};return tuple(m.setdefault(x^y,len(m)) for x,y in zip(p,p[1:]))
for s in (r/'uniqthree.pts').read_text().splitlines():
 for p in parse(s):
  bank[len(p)][min(norm(p),norm(p[::-1]))]=p
bank={k:list(v.values()) for k,v in bank.items()}
rng=random.Random(7112301);splits=[(a,b,c) for a in bank for b in bank for c in bank if 7<=a<=b<=c and 101<=a+b+c<=103 and c<84]
with (r/'cross3.pts').open('w') as f:
 for i in range(5000):
  lens=rng.choice(splits);parts=[rng.choice(bank[k]) for k in lens];print(' '.join(' '.join(map(str,[len(p),*p])) for p in parts),file=f)
print('shapes',sum(map(len,bank.values())),'partitions',len(splits))

