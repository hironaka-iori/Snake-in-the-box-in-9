from prep import *
rows=[];meta=[]
for s in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt'):
 p=list(map(int,s.split()))
 if len(p)!=192:continue
 alt={i:p[i]^p[i-1]^p[i+1] for i in range(8,len(p)-8)}
 flips=[i for i,x in alt.items() if x not in p and all((x^v).bit_count()!=1 for j,v in enumerate(p) if abs(j-i)!=1)]
 chosen=False
 for i,j,k in combinations(flips,3):
  if min(j-i,k-j)<10:continue
  a=p[:]
  for l in (i,j,k):a[l]=alt[l]
  b=p[2:-2];a=a[1:-1]
  if not ok(a):continue
  rows.extend([a,b]);meta.append((i,j,k));chosen=True;break
 if len(meta)>=3:break
dump(r/'ctrl3.pts',rows);print('controls',meta)

