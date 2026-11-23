from pathlib import Path
from collections import Counter
from physical_sat import solve
from setup import read,check
r=Path(__file__).resolve().parent
s=Counter();out=[]
for i,p in enumerate(read(r/'walks.pts')):
 st,q=solve(p,[0,1,2],12000);s[st]+=1
 if q:check(q,192);out.append((i,q))
assert not out
print(s)

