from pathlib import Path
from subprocess import run
from itertools import cycle
from random import Random
r=Path(__file__).resolve().parent
rows=[s for s in Path('/tmp/q8_record_forests20.pts').read_text().splitlines()]
pools={}
for s in rows:
 z=list(map(int,s.split()));a=z[0];b=z[a+1]
 if a+b>=98:pools.setdefault(min(a,b),[]).append(s)
seed=(r/'seed.pts').read_text().strip()
jobs=[(seed,22),(seed,28)]
for k,aim in [(4,5),(14,16),(43,43),(48,47),(3,3),(49,45),(4,4),(14,13),(43,44),(48,42),(49,49),(3,6),(14,17),(43,40),(4,8),(49,48)]:
 jobs.append((pools[k][0],aim))
for i,(src,aim) in enumerate(jobs):
 sp=r/f'other{i}.seed';sp.write_text(src+'\n')
 with (r/f'targ{i}.pts').open('w') as f,(r/f'targ{i}.log').open('w') as l:
  run([str(r/'target'),str(sp),str(17),str(80172355+i*837),str(.46 if i%2 else .72),str(19513 if i%3 else 33831),str(aim)],stdout=f,stderr=l,check=True)

