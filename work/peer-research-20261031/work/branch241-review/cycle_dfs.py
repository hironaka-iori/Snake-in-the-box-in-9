"""Independent depth-first enumeration of induced cube cycles containing a fixed path."""
import time
from geometry_check import verify_cycle

def enumerate_cycles(prefix,length,n=9,allowed=None):
 prefix=list(prefix)
 if length<4 or length%2 or len(prefix)>length:raise ValueError('invalid length')
 for i,a in enumerate(prefix):
  for j in range(i+1,len(prefix)):
   if ((a^prefix[j]).bit_count()==1)!=(j==i+1):raise ValueError('prefix is not induced')
 if len(set(prefix))!=len(prefix):raise ValueError('duplicate prefix')
 allowed=set(range(1<<n)) if allowed is None else set(allowed)
 nbr=[sum(1<<(v^(1<<d)) for d in range(n)) for v in range(1<<n)];start=prefix[0];path=prefix[:];out=set();nodes=0
 def dfs(mask):
  nonlocal nodes
  nodes+=1;v=path[-1];left=length-len(path)
  if left==0:
   if (v^start).bit_count()==1:out.add(tuple(sorted(path)))
   return
  if (v^start).bit_count()>left+1:return
  for d in range(n):
   w=v^(1<<d)
   if w not in allowed or mask>>w&1:continue
   adjacency=nbr[w]&mask
   if left==1:
    if adjacency!=((1<<v)|(1<<start)):continue
   elif adjacency!=1<<v:continue
   path.append(w);dfs(mask|1<<w);path.pop()
 dfs(sum(1<<v for v in prefix))
 for c in out:verify_cycle(c,n)
 return sorted(out),{'nodes_visited':nodes,'cycles':len(out),'length':length,'prefix':prefix}
if __name__=='__main__':
 import json
 from pathlib import Path
 t=time.perf_counter();cycles,meta=enumerate_cycles([0,1,17],8);meta['seconds']=time.perf_counter()-t
 Path(__file__).with_suffix('.json').write_text(json.dumps({'meta':meta,'cycles':cycles},indent=2));print(json.dumps(meta,indent=2))
