from prepare import *
from collections import Counter
def canon(w):
 def norm(s):
  f={};return ''.join(str(f.setdefault(c,len(f))) for c in s)
 return min(norm(w),norm(w[::-1]))
def word(q):return ''.join(str((v^w).bit_length()-1) for v,w in zip(q,q[1:]))
def path_from(s):
 deg={v:len(N[v]&s) for v in s}
 if not all(1<=d<=2 for d in deg.values()):return None
 ends=[v for v in s if deg[v]==1]
 if len(ends)!=2:return None
 p=ends[:1];rem=s-{p[0]}
 while rem:
  nxt=N[p[-1]]&rem
  if not nxt:return None
  v,=nxt;rem.remove(v);p.append(v)
 assert valid(p);return p
def run():
 cs=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()));ref={canon(w) for w in (R/'q9_gap_generations/prior191.words').read_text().splitlines()};found=[]
 for mode in ['cold','warm','blend']:
  for record in (D/(mode+'.log')).read_text().splitlines():
   z=record.split();i=int(z[1]);mask=sum(int(v)<<(64*j) for j,v in enumerate(z[12:20]));s=unpack(format(mask,'x'));fixed=unpack(cs[i]['anchor'])
   deg={v:len(N[v]&s) for v in s};bad=[v for v in s if deg[v]>2]
   for u in s-fixed:
    if any(u!=b and u not in N[b] for b in bad):continue
    p=path_from(s-{u})
    if p:
     w=canon(word(p));found.append(dict(case=i,mode=mode,removed=u,known=w in ref,canonical=w,vertices=p))
 (D/'salvage.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in found));print(len(found),len({r['canonical'] for r in found}),len({r['canonical'] for r in found if not r['known']}),Counter(r['mode'] for r in found))
if __name__=='__main__':run()
