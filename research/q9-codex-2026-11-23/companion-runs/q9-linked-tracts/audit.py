from pathlib import Path
import json,gzip
from collections import Counter
from prep import r,ws,ok,shape
known={shape(p) for l in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt') if len(p:=list(map(int,l.split())))==192};assert len(known)==131
results={};novel=[]
for name in ['ctrl.out','r192.out','sweep.out','mid.out','real191.pts','mid191.pts','deep.out','deep191.pts','triple.out','triple191.pts']:
 f=r/name
 if not f.exists():continue
 rows=[];new=[];classes=set()
 for s in f.read_text().splitlines():
  i,*p=map(int,s.split());assert ok(p);keys=shape(p);classes.add(keys);rows.append(len(p)-1)
  if len(p)>=193 or keys not in known:
   new.append(i);ext=[]
   if len(p)==192:
    for q in (p,p[::-1]):
     for d in range(9):
      x=q[-1]^(1<<d)
      if x in q or any((w^x).bit_count()==1 for w in q[:-1]):continue
      ext.append(q+[x])
    for a in ext:assert ok(a)
   novel.append(dict(file=name,row=i,vertices=p,extensions=ext))
 results[name]=dict(lengths=dict(Counter(rows)),classes=len(classes),new=new)
logs={}
for f in r.glob('*.log'):
 s=f.read_text().strip()
 if s:logs[f.name]=s
(r/'audit.json').write_text(json.dumps(dict(results=results,logs=logs),indent=2)+'\n')
if novel:(r/'novel.json').write_text(json.dumps(novel)+'\n')
print(results)

