from direct import *
from families import norm,steps
from hitting import residual
def get_refs():
 dd={}
 for f in sorted(D.glob('*.work')):
  if not f.name[1:4].isdigit():continue
  for ix,s in enumerate(f.read_text().splitlines()):
   row,d,t,a,j,L,R0,rem,np,k,*v=map(int,s.split());dd[f.stem,ix]=dict(label=f.stem,ix=ix,row=row,d=d,t=t,a=a,j=j,L=L,R=R0,rem=rem,p=v[k:],blocked=v[:k])
 return dd
def go():
 data=[json.loads(s) for s in (D/'families.jsonl').read_text().splitlines()]; ref=get_refs();rng=random.Random(721965);excluded=residual();runs=[]
 for i,(w,links) in enumerate(data):
  if i in excluded:continue
  rng.shuffle(links);used=set()
  for fname,ix in links:
   gain=192-int(fname[1:4])
   if gain in used:continue
   used.add(gain);c=ref[fname,ix];ax=active(c);must=set(c['blocked']);options=[]
   if gain in (2,4):
    options += [{x:gain} for x in ax if must<={x}]
   for g in (2,4):
    if gain-g not in (2,4):continue
    options += [{x:g,y:gain-g} for x,y in itertools.combinations(ax,2) if must<={x,y}]
   rng.shuffle(options)
   ranks=list(range(max(0,c['rem']-max(0,c['R'].bit_count()-1)),min(c['rem'],max(0,c['L'].bit_count()-1))+1))
   rng.shuffle(ranks)
   for det in options[:3]:
    for l in ranks[:2]:runs.append([i,c,det,l])
 rng.shuffle(runs);(D/'wide.jsonl').write_text(''.join(json.dumps(z,separators=(',',':'))+'\n' for z in runs))
 for k,(i,c,det,l) in enumerate(runs):
  z,p=solve(c['p'],c['L'],c['R'],l,c['rem']-l,det,2000)
  print(json.dumps([k,i,z,p],separators=(',',':')),flush=True)
  if p:assert len(p)==193;break
if __name__=='__main__':go()
