from pathlib import Path
import itertools,os,json,subprocess,concurrent.futures as C
d=Path('q9_fresh_mother_lifts_20261120')
tasks=[]
for src,size in [('q8_fresh_99_forests.pts',99),('q8_dense_forest_bank_round2.pts',100)]:
 for goal in range(192,96+size):
  num=size+95-goal; forests=set()
  for line in Path(src).read_text().splitlines():
   row=list(map(int,line.split()));n=row[0];a=row[1:n+1];r=row[n+1];b=row[n+2:];assert r==len(b)
   for a0 in range(num+1):
    for a1 in range(num-a0+1):
     for b0 in range(num-a0-a1+1):
      b1=num-a0-a1-b0;left=tuple(a[a0:len(a)-a1]);right=tuple(b[b0:len(b)-b1])
      if left and right:forests.add((left,right))
  dest=d/f'all_four_ends_{size}_{goal}.pts'
  with dest.open('w') as out:
   for a,b in sorted(forests):print(len(a),*a,len(b),*b,file=out)
  for h in (3,5,7):tasks.append((str(dest),size,goal,h))
def run(item):
 f,size,t,h=item
 with (d/f'allfour461_{size}_{t}_{h}.log').open('w') as log:
  p=subprocess.run(['/private/tmp/q9_salvage20',str(d/'q8_joint_461_increments.words'),'q8_catalogue_96_98.words',str(t),'95',str(h),'0','0'],env={**os.environ,'Q9_FOREST_BANK':f,'Q9_ONLY_FOREST_BANK':'1'},stdout=log,stderr=subprocess.STDOUT)
 return p.returncode
with C.ThreadPoolExecutor(6) as pool:print(list(pool.map(run,tasks)))
