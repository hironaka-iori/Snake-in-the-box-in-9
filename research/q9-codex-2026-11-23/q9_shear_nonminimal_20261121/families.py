from prepare import *
from functools import lru_cache
def steps(p):return tuple(a^b for a,b in zip(p,p[1:]))
@lru_cache(100000)
def norm(ws):
 special=next((x for x in ws if x.bit_count()>1),0);axes={};pattern=[];M=0
 for x in ws:
  if x.bit_count()>1:
   assert x==special;pattern.append(9)
  else:
   if x not in axes:axes[x]=len(axes)
   k=axes[x];pattern.append(k)
   if x&special:M|=1<<k
 return bytes([special.bit_count(),M%256,M//256,*pattern])
def sig(w):return min(norm(w),norm(w[::-1]))
def reconstruct(w):
 p=[0]
 for x in w:p.append(p[-1]^x)
 return p
def build():
 family={};n=0
 for fn in sorted(D.glob('*.work')):
  stats=(D/(fn.stem+'.log')).read_text().splitlines();assert len(stats)==131
  for i,s in enumerate(fn.read_text().splitlines()):
   row,d,t,a,j,L,R,rem,np,k,*vals=map(int,s.split());c=vals[k:];w=steps(c);key=sig(w);n+=1
   if key not in family:family[key]=[w,[]]
   family[key][1].append([fn.stem,i])
 roots=sorted(family.values(),key=lambda r:(len(r[0]),-len(r[1]),r[0]));(D/'families.jsonl').write_text(''.join(json.dumps([w,refs],separators=(',',':'))+'\n' for w,refs in roots));print(n,len(roots))
if __name__=='__main__':build()
