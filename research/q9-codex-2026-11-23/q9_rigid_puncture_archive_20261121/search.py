from pathlib import Path
from itertools import permutations
from collections import defaultdict,Counter
import json
D=Path(__file__).resolve().parent;R=D.parent
def walk(w):
 p=[0]
 for c in w:p.append(p[-1]^(1<<int(c)))
 return p
def norm(w):
 f={};return bytes(f.setdefault(c,len(f)) for c in w)
def true(p):
 if len(set(p))!=len(p):return False
 m={x:i for i,x in enumerate(p)}
 return all({m[x^(1<<k)] for k in range(9) if x^(1<<k) in m}=={j for j in (i-1,i+1) if 0<=j<len(p)} for i,x in enumerate(p))
def embed(x,axes):
 y=0
 while x:
  k=x&-x;y^=1<<axes[k.bit_length()-1];x-=k
 return y
def geom(p,w,hole):
 n=len(p)
 if hole>=n-hole-1:a,b=0,hole-1
 else:a,b=hole+1,n-1
 return a,b,w[a:b]
def main():
 ws=(R/'q8_catalogue_96_98.words').read_text().split();B=[walk(w) for w in ws]
 ar=(R/'q9_gap_generations/prior191.words').read_text().split();assert ar==(R/'q9_far189_spring_20261121/comparison191.words').read_text().split()
 P=[walk(w) for w in ar];S=list(map(set,P));assert len(P)==131 and all(len(p)==192 and true(p) for p in P)
 rigid=[i for i,p in enumerate(B) if set(p)|{v^(1<<d) for v in p[1:-1] for d in range(8)}==set(range(256))]
 assert len(rigid)==41 and all(true(B[i]) and len(B[i])==97 for i in rigid)
 requests=defaultdict(list)
 for i in rigid:
  for h in range(97):
   a,b,z=geom(B[i],ws[i],h)
   for flipped,u in [(False,z),(True,z[::-1])]:
    requests[len(u),norm(u)].append((i,h,a,b,flipped,u))
 counts=Counter();hits=[];masks=defaultdict(set);tried=Counter();index=defaultdict(list)
 for n,nw in sorted(requests):
  index[n].append(nw)
 for n,keys in index.items():
  wanted=set(keys)
  for r,q in enumerate(P):
   for k in range(192-n):
    frag=ar[r][k:k+n];key=norm(frag)
    if key not in wanted:continue
    for i,h,a,b,rev,fromword in requests[n,key]:
     counts['oriented_anchor_matches']+=1
     assignment={int(x):int(y) for x,y in zip(fromword,frag)}
     unused=sorted(set(range(8))-set(assignment));free=sorted(set(range(9))-set(assignment.values()))
     for ext in permutations(free,len(unused)):
      f=assignment|dict(zip(unused,ext));axes=tuple(f[x] for x in range(8));off=q[k]^embed(B[i][b if rev else a],axes)
      miss=off^embed(B[i][h],axes);counts['isometries']+=1;tried[i,h]+=1
      if miss in S[r]:
       counts['omission_present']+=1;continue
      if any((off^embed(x,axes)) not in S[r] for j,x in enumerate(B[i]) if j!=h and not a<=j<=b):continue
      nrm=axes+(next(iter(set(range(9))-set(axes))),);inv=tuple(nrm.index(k) for k in range(9));fixed=[embed(x^off,inv) for x in q]
      assert true(fixed) and max(B[i])<256 and set(B[i])-set(fixed)=={B[i][h]}
      opposite=(B[i][h]^256) in fixed
      hits.append(dict(donor=i,hole=h,vertex=B[i][h],archive=r,anchor=[a,b],archive_start=k,reverse=rev,axes=axes,translation=off,missing_opposite_occupied=opposite,layer_visits=sum((u^v)==256 for u,v in zip(fixed,fixed[1:]))+1,layer_population=sum(x<256 for x in fixed),vertices=fixed));masks[i,h,r].add(tuple(sorted(fixed)))
 (D/'hits.jsonl').write_text(''.join(json.dumps(v,separators=(',',':'))+'\n' for v in hits))
 clean={(z['donor'],z['hole'],z['archive']) for z in hits};five={43,44,464,472,576}
 print(json.dumps(dict(rigid=rigid,archive=len(P),donor_holes=41*97,archive_donor_hole_triples=41*97*131,anchor_lengths=sorted(index),triple_hits=len(clean),actual_embeddings=len(hits),distinct_placed_sets=sum(len(x) for x in masks.values()),donor_holes_hit=sorted({(i,h) for i,h,r in clean}),archives=sorted({r for i,h,r in clean}),per_donor=dict(Counter(i for i,h,r in clean)),five_hits=sum(i in five for i,h,r in clean),matching_anchor_donor_holes=len(tried),counts=counts),indent=2))
if __name__=='__main__':main()
