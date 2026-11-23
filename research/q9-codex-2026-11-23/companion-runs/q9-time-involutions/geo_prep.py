from prep import *
src=[list(map(int,l.split())) for l in (r/'ctrl_truth.pts').read_text().splitlines()];out=[]
for p in src:
 q=p[:]
 for pos in (4,37,78,111,152):
  for l in range(pos,pos+15):
   acts=[p[i]^p[i+1] for i in range(l,l+4)]
   if len(set(acts))<4:continue
   v=p[l]
   for at,m in enumerate(acts[::-1]):v^=m;q[l+at+1]=v
   break
 assert not valid(q) and all((x^y).bit_count()==1 for x,y in zip(q,q[1:]))
 out.append(q)
dump(r/'geocontrol.pts',out)

