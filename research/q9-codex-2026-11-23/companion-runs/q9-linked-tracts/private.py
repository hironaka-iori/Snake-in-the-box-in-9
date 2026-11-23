from prep import *
from collections import Counter
from pathlib import Path
import json
def load_pairs(f):
 a=[list(map(int,l.split())) for l in f.open()];return list(zip(a[::2],a[1::2]))
bank=load_pairs(r/'pairs.pts');middle=load_pairs(r/'middles.pts')
known={shape(p) for l in gzip.open(ws/'q9_free_bridge_join_inputs.txt.gz','rt') if len(p:=list(map(int,l.split())))==192}
report={};union={};privateBoth=set()
for nm,db in [('real191.pts',bank),('mid191.pts',middle),('deep191.pts',middle),('triple191.pts',middle),('ctrl3.out',middle)]:
 f=r/nm
 if not f.exists():continue
 detail=[]
 for l in f.read_text().splitlines():
  j,*p=map(int,l.split());assert ok(p);A,B=db[j];assert ok(A) and ok(B) and shape(A)!=shape(B);SA=set(A);SB=set(B);S=set(p);k=shape(p)
  nA=len(S&(SA-SB));nB=len(S&(SB-SA));out=len(S-SA-SB);detail.append([j,nA,nB,out,k==shape(A),k==shape(B),k in known]);union[k]=p
  if nA and nB:privateBoth.add(k)
 report[nm]=detail
novel=[p for k,p in union.items() if k not in known];report['union_191_classes']=len(union);report['using_vertices_private_to_each_parent_classes']=len(privateBoth);report['outside131']=len(novel)
(r/'parents_audit.json').write_text(json.dumps(report,indent=2)+'\n');print('classes',len(union),'private_both',len(privateBoth),'new',len(novel));print(report.get('triple191.pts'))

