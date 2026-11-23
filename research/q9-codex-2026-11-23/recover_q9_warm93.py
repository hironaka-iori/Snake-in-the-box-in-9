import glob,sys
from pathlib import Path
import json
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0,str(Path('q9_fresh_mother_lifts_20261120').resolve()))
from two_free_tails_sat import search
def work(t):
 degree,p,q,ep=t
 # Translate back to root zero, retaining the same coordinate labels.
 m=p[0];w=''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))
 return [degree,search(w,192,ep,'cadical195',45000,[x^m for x in q])]
if __name__=='__main__':
 cases={}
 for fn in glob.glob('q9_warm93_*.log'):
  for l in open(fn):
   if not l.startswith('WARM '):continue
   h,z=l.split(' mid ');_,i,k=h.split();a,b=z.split(' forest')
   p,q=list(map(int,a.split())),list(map(int,b.split()));old=cases.get(i)
   if old is None or old[0]>int(k):cases[i]=(int(k),p,q)
 jobs=[(*v,ep) for v in sorted(cases.values()) for ep in [0,1]]
 print(json.dumps(dict(jobs=len(jobs))),flush=True)
 with ProcessPoolExecutor(2) as pool:
  for r in pool.map(work,jobs):
   print(json.dumps(r,separators=(',',':')),flush=True)
   if r[1].get('path'):break

