"""Complete induced-8-cycle enumeration inside an arbitrary Qn vertex domain.
Every induced 8-cycle spans a unique Q4 face. Exhaust all 16-choose-8 Q4 subsets,
retain the connected induced degree-two subsets, then embed into each Q4 face.
No SAT solver, floating point, or external dependencies are used.
"""
from itertools import combinations
from functools import lru_cache
from pathlib import Path
from collections import Counter
import argparse,gzip,json,time


def validate_cycle(vertices,n=9):
 C=tuple(vertices)
 if not isinstance(n,int) or isinstance(n,bool) or n<1:raise ValueError('positive integer dimension required')
 if any(not isinstance(v,int) or isinstance(v,bool) or not 0<=v<1<<n for v in C):raise ValueError('cycle vertex outside the declared cube')
 if len(C)!=8 or len(set(C))!=8:raise ValueError('eight distinct vertices required')
 adj={x:[y for y in C if (x^y).bit_count()==1] for x in C}
 if any(len(vs)!=2 for vs in adj.values()):raise ValueError('not induced degree two')
 seen={C[0]};todo=[C[0]]
 while todo:
  for w in adj[todo.pop()]:
   if w not in seen:seen.add(w);todo.append(w)
 if len(seen)!=8:raise ValueError('not connected')
 return True

@lru_cache(None)
def templates():
 out=[]
 for C in combinations(range(16),8):
  try:validate_cycle(C,4)
  except ValueError:continue
  out.append(C)
 assert len(out)==168
 return tuple(out)


def enumerate_all8(allowed,n=9,verify_each=True):
 start=time.perf_counter();allowed=set(allowed)
 if not isinstance(n,int) or isinstance(n,bool) or n<4 or any(not isinstance(v,int) or isinstance(v,bool) or not 0<=v<1<<n for v in allowed):raise ValueError('invalid cube dimension or domain')
 ts=templates();cycles=[];faces=0;full=0
 for ds in combinations(range(n),4):
  free=sum(1<<d for d in ds);mapping=[sum((1<<ds[j]) for j in range(4) if v>>j&1) for v in range(16)]
  for base in range(1<<n):
   if base&free:continue
   faces+=1;translation=[base|offset for offset in mapping]
   for t in ts:
    full+=1;c=tuple(translation[v] for v in t)
    if not all(v in allowed for v in c):continue
    if verify_each:validate_cycle(c,n)
    cycles.append(c)
 assert len(cycles)==len(set(cycles)),'duplicate embeddings contradict unique affine span'
 cycles.sort()
 return cycles,{'dimension':n,'domain_vertices':len(allowed),'Q4_subsets_exhausted':12870,'induced_Q4_templates':len(ts),'Q4_faces':faces,'full_cube_cycles_considered':full,'retained_cycles':len(cycles),'each_retained_cycle_independently_validated':verify_each,'seconds':time.perf_counter()-start}


def main():
 ap=argparse.ArgumentParser();ap.add_argument('--centre',type=int,default=1);ap.add_argument('--radius',type=int,default=4);ap.add_argument('--dimension',type=int,default=9);ap.add_argument('--out',type=Path,default=Path(__file__).parent/'all8_B4_manifest.json.gz');args=ap.parse_args()
 allowed=[v for v in range(1<<args.dimension) if (v^args.centre).bit_count()<=args.radius];cycles,meta=enumerate_all8(allowed,args.dimension)
 meta.update(centre=args.centre,radius=args.radius)
 if args.dimension==9 and args.radius==4:assert len(cycles)==77868
 with gzip.open(args.out,'wt',encoding='utf-8') as f:json.dump({'meta':meta,'cycles':cycles},f,separators=(',',':'))
 args.out.with_suffix('.summary.json').write_text(json.dumps(meta,indent=2));print(json.dumps(meta,indent=2))
if __name__=='__main__':main()

