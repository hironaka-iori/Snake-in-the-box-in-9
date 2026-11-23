from pathlib import Path
import sys,json,collections,itertools
D=Path(__file__).resolve().parent;R=D.parent;OLD=R/'q9_partial_geodesic_dp_20261121'
def cases():
 old=[]
 for name in ('head','tail','integral'):
  for ix,line in enumerate((OLD/(name+'.work')).read_text().splitlines()):
   row,d,t,a,j,L,R0,rem,n,*p=map(int,line.split());old.append(dict(label=name,ix=ix,row=row,d=d,t=t,a=a,j=j,L=L,R=R0,rem=rem,p=p))
 return old
def key(r):
 def on(p,L,R):
  start=p[0];masks=[L]+[x^y for x,y in zip(p,p[1:])]+[R]
  perm=sorted(range(9),key=lambda i:tuple(m>>i&1 for m in masks))
  def f(x):return sum((x>>a&1)<<k for k,a in enumerate(perm))
  return tuple(f(m) for m in masks)
 return min(on(r['p'],r['L'],r['R']),on(r['p'][::-1],r['R'],r['L']))
def prep():
 o=cases();groups={}
 for i,r in enumerate(o):groups.setdefault(key(r),[]).append(i)
 out=[]
 for v in groups.values():out.append(dict(**o[v[0]],equiv=v))
 (D/'cases.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in out));print(len(o),len(out))
if __name__=='__main__':prep()
