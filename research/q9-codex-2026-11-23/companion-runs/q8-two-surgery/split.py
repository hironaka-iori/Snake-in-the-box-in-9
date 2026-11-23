from pathlib import Path
from itertools import accumulate
from collections import Counter
import operator,sys
r=Path(__file__).resolve().parent
words={}
for f in [*Path.cwd().glob('q8*.txt'),*Path.cwd().glob('q8*.words')]:
 for w in f.open():
  w=w.strip()
  if len(w)<96 or not set(w)<=set('01234567'):continue
  p=list(accumulate((1<<int(c) for c in w),operator.xor,initial=0))
  if len(set(p))!=len(p) or any(((x^y).bit_count()==1)!=(j==i+1) for i,x in enumerate(p) for j,y in enumerate(p) if j>i):continue
  words[w]=p
def row(a,b):return ' '.join(map(str,[len(a),*a,len(b),*b]))
for l in [96,97,98]:
 with (r/f'split{l}.pts').open('w') as f:
  for w,p in words.items():
   if len(w)!=l:continue
   for i in range(1,len(p)-1):print(row(p[:i],p[i+1:]),file=f)
print(Counter(map(len,words)))

