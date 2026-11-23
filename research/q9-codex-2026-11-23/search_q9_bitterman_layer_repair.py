"""Rank historical rooted Q8 donor pairs by minimum overlap and repair both layers."""
import json,itertools,sys
from concurrent.futures import ProcessPoolExecutor
def placements():
 import numpy as np
 from search_q9_long_arm_anywhere import arms
 donors=[r["vertices"] for r in json.load(open("q8_bitterman_97.json"))["rows"]]
 targets=[p for _,p in arms() if len(p)>=98]+donors
 bitperms=np.array(list(itertools.permutations(1<<d for d in range(8))),dtype=np.uint16)
 images=np.zeros((len(bitperms),256),np.uint8)
 for v in range(1,256):
  b=v&-v;images[:,v]=images[:,v-b]^bitperms[:,b.bit_length()-1]
 def root(q,rev):
  if rev:q=q[::-1]
  return [v^q[0] for v in q]
 def mask(q):
  m=np.zeros(256,np.uint8);m[q]=1;return m
 pop=np.array([v.bit_count() for v in range(256)],np.uint8)
 lower=[(i,r,p,np.packbits(mask(p))) for i,u in enumerate(donors) for r in range(2) for p in [root(u,r)]]
 for j,b in enumerate(targets):
  for s in range(2):
   q=root(b,s);packed=np.packbits(mask(q)[images],axis=1)
   for i,r,p,m in lower:
    ov=pop[packed&m].sum(axis=1);k=int(ov.argmin())
    inv=np.argsort(images[k]);out=[int(inv[v]) for v in q]
    assert len(set(p)&set(out))==int(ov[k])
    yield [int(ov[k]),i,r,j,s,p,out]
def attempt(z):
 from search_q9_anchored_sets import search
 from verify_q9_center_avoidance import verify
 h,i,r,j,s,p,q,rad,a,b=z
 coll=(set(p)&set(q))-{0}
 fixed={0,256};seed=set(p)|{256+v for v in q}
 for path,offset in [(p,0),(q,256)]:
  bad=[t for t,v in enumerate(path) if v in coll]
  fixed.update(v+offset for t,v in enumerate(path) if all(abs(t-y)>rad for y in bad))
 st,w=search(fixed,seed,a+b+1,10000,rooted_layer_lengths=(a,b))
 if w:
  verify(w);assert len(w)==a+b+2 and sum(x<256 for x in w)==a+1 and sum(x^y==256 for x,y in zip(w,w[1:]))==1
 return [h,i,r,j,s,rad,a,b,len(fixed),st,w]
if __name__=="__main__":
 if sys.argv[1]=="place":
  for z in placements():print(json.dumps(z,separators=(",",":")),flush=True)
 else:
  from search_q9_two_free_colours import templates
  a,b=templates()[0]
  z=attempt([1,-1,0,-1,0,a,b,0,len(a)-1,len(b)-1]);assert z[-2]=="FOUND" and len(z[-1])==192
  print(json.dumps(z),flush=True)
  seen=set();jobs=[]
  for z in sorted(map(json.loads,open("q8_bitterman_min_overlaps.jsonl"))):
   k=frozenset((frozenset(z[-2]),frozenset(z[-1])))
   if k in seen:continue
   seen.add(k)
   for rad in (1,2,4):
    for a,b in [(96,95),(95,96),(97,97),(98,97)]:jobs.append(z+[rad,a,b])
   if len(seen)>=72:break
  with ProcessPoolExecutor(2) as pool:
   for z in pool.map(attempt,jobs):
    print(json.dumps(z,separators=(",",":")),flush=True)
    if z[-1]:break
