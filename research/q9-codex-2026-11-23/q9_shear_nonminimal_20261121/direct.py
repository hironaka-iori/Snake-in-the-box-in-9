from prepare import *
from detour import solve
import random
def fresh():
 out=[]
 for fn in ('i190','f190','i188','f188'):
  for ix,line in enumerate((D/(fn+'.work')).read_text().splitlines()):
   row,d,t,a,j,L,R0,rem,np,k,*vals=map(int,line.split());blocked=vals[:k];p=vals[k:];out.append(dict(label=fn,ix=ix,row=row,d=d,t=t,a=a,j=j,L=L,R=R0,rem=rem,p=p,blocked=blocked))
 return out
def active(r):
 p=r['p'];return [i for i in range(len(p)-1) if (p[i]^p[i+1]).bit_count()>1]
def jobs():
 rng=random.Random(83913);groups={};raw=fresh();rng.shuffle(raw)
 for r in raw:
  if r['label'].endswith('190') and len(r['blocked'])>1:continue
  groups.setdefault((r['label'][-3:],key(r)),r)
 rows=list(groups.values());rng.shuffle(rows);return rows
def profiles(r):
 pool=active(r);b=r['blocked'];gain=192-int(r['label'][-3:]);choices=[]
 if len(b)<=1:
  choices.extend({i:gain} for i in (b if b else pool))
 if gain==4:
  choices.extend({i:2,j:2} for i,j in itertools.combinations(pool,2) if set(b)<={i,j})
 return choices
def sample():
 rng=random.Random(540127);rows=jobs();out=[]
 for i,r in enumerate(rows):
  opts=profiles(r);rng.shuffle(opts)
  for det in opts[:2]:
   use=list(range(max(0,r['rem']-max(0,r['R'].bit_count()-1)),min(r['rem'],max(0,r['L'].bit_count()-1))+1));rng.shuffle(use)
   for l in use[:1]:
    out.append(dict(**r,det=det,l=l,r=r['rem']-l))
 rng.shuffle(out);return out
def run():
 if sys.argv[1]=='prepare':
  q=sample();(D/'direct.jsonl').write_text(''.join(json.dumps(v,separators=(',',':'))+'\n' for v in q));print(len(q));return
 if sys.argv[1]=='control':
  rows=(OLD/'control.work').read_text().splitlines()
  for mark in (1,2):
   found=False
   for ix,line in enumerate(rows):
    row,d,t,a,j,L,R,rem,n,*p=map(int,line.split());pool=active({'p':p})
    if len(pool)<2 or max(0,L.bit_count()-1)>=rem or max(0,R.bit_count()-1)>=rem:continue
    for chosen in itertools.combinations(pool,mark):
     det={i:(4 if k==0 else 2) for k,i in enumerate(chosen)}
     for l in range(max(1,rem-(R.bit_count()-1)),min(rem-1,L.bit_count()-1)+1):
      st,w=solve(p,L,R,l,rem-l,det,20000)
      if w:
       print(json.dumps(dict(ix=ix,det=det,l=l,r=rem-l,w=w)),flush=True);found=True;break
     if found:break
    if found:break
   assert found
  return
 lim=int(sys.argv[2]);budget=int(sys.argv[3])
 for i,line in enumerate((D/'direct.jsonl').read_text().splitlines()[:lim]):
  r=json.loads(line);det={int(i):q for i,q in r['det'].items()};st,w=solve(r['p'],r['L'],r['R'],r['l'],r['r'],det,budget);print(json.dumps([i,st,w],separators=(',',':')),flush=True)
  if w:assert len(w)==193;return
if __name__=='__main__':run()
