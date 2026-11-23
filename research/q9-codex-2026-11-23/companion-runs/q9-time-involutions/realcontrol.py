from pathlib import Path
from collections import Counter
import csv,random
from prep import valid
r=Path(__file__).resolve().parent;rng=random.Random(9371)
rows=[];counts=Counter()
for row in csv.DictReader(open('/tmp/q9_all190_20261119.csv')):
 p=list(map(int,row['vertices'].split()))
 for rev in (0,1):
  if rev:p.reverse()
  for d in range(9):
   y=p[-1]^(1<<d)
   if y in p:continue
   bad=sum((y^x).bit_count()==1 for x in p[:-1])
   if bad not in (1,2):continue
   rows.append(p+[y]);counts[bad]+=1
rng.shuffle(rows);(r/'realctrl.pts').write_text(''.join(' '.join(map(str,p))+'\n' for p in rows));print(counts)

