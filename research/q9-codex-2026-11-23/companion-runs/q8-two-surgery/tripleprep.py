from pathlib import Path
from itertools import groupby
from collections import Counter
import csv
r=Path(__file__).resolve().parent;seen=set();stats=Counter()
with (r/'triples.pts').open('w') as out:
 for file in Path('/tmp').glob('q9*csv'):
  if file.stat().st_size>10**7:continue
  try:
   for row in csv.DictReader(file.open()):
    if row.get('n')!='9' or 'vertices' not in row:continue
    p=list(map(int,row['vertices'].split()))
    if len(set(p))!=len(p):continue
    for i in range(9):
     trans=lambda x:(x&((1<<i)-1))|((x>>(i+1))<<i)
     groups=[[],[]]
     for bit,g in groupby(p,key=lambda x:(x>>i)&1):
      groups[bit].append([trans(x) for x in g])
     for ls in groups:
      ls=sorted(ls,key=len,reverse=True)
      if len(ls)<3:continue
      for last in range(2,len(ls)):
       if sum(map(len,[ls[0],ls[1],ls[last]]))<98:break
       for b in range(1,last):
        for a in range(b):
         w=[ls[a],ls[b],ls[last]];n=sum(map(len,w))
         if n<98:continue
         zero=w[0][0];key=tuple(z for q in w for z in (len(q),*[x^zero for x in q]))
         if key in seen:continue
         seen.add(key);stats[n]+=1;print(*key,file=out)
  except (ValueError,KeyError):continue
print(stats)

