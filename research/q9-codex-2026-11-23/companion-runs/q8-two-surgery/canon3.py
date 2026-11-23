from pathlib import Path
from itertools import permutations,product
from collections import Counter
from verify import parse
import sys
r=Path(__file__).resolve().parent;seen=set();counts=Counter();rows=[]
for line in (r/'threebank.pts').read_text().splitlines():
 paths=parse(line)
 if len(paths)!=3:continue
 # Degree/adjacency check against the three component records.
 occupied={x for p in paths for x in p}
 assert len(occupied)==sum(map(len,paths))
 for p in paths:
  for i,x in enumerate(p):
   expected=set(p[max(0,i-1):i]+p[i+1:i+2]);assert {x^(1<<d) for d in range(8)}&occupied==expected
 sizes=sorted(map(len,paths));best=None
 for ar in permutations(paths):
  if list(map(len,ar))!=sizes:continue
  for ds in product(range(2),repeat=3):
   oriented=[a[::-1] if d else a for a,d in zip(ar,ds)];m={}
   steps=tuple(tuple(m.setdefault(x^y,len(m)) for x,y in zip(a,a[1:])) for a in oriented);off=oriented[0][0]
   # For axes absent in all paths retain them jointly via sorted two-component bit patterns.
   dis=[a[0]^off for a in oriented[1:]];known=tuple(sum(1<<d for axis,d in m.items() if x&axis) for x in dis)
   un=tuple(sorted(tuple((x>>i)&1 for x in dis) for i in range(8) if 1<<i not in m))
   key=(steps,known,un)
   if best is None or key<best:best=key
 if best in seen:continue
 seen.add(best);total=sum(sizes);counts[total]+=1;rows.append((total,line))
rows.sort(key=lambda a:-a[0]);(r/'uniqthree.pts').write_text('\n'.join(l for n,l in rows)+'\n');print(len(rows),counts)

