from run import *
from prep import word
known={min(word(q),word(q[::-1])) for l in __import__('gzip').open(ws/'q9_free_bridge_join_inputs.txt.gz','rt') if len(q:=list(map(int,l.split())))==192}
bank=[list(map(int,l.split()))[3:] for l in (r/'parents.pts').open()];rows=[[[int(z) for z in l.split()] for l in (r/nm).open()] for nm in ('grafts.pts','exact.pts')]
cnt=Counter()
with (r/'retry191.jsonl').open('w',1) as f:
 for l in (r/'rank191.jsonl').open():
  g,i,score,st,_,_=json.loads(l)
  if st!='UNKNOWN':continue
  a,b,m,v,*_=rows[g][i];h=combine(bank[a],bank[b],m,v);st,p=solve(h,191,200000);classification=None
  if p:
   verify(p);assert len(p)==192;classification='known' if min(word(p),word(p[::-1])) in known else 'new'
   if classification=='new':
    ext=[z+[v] for z in [p,p[::-1]] for d in range(9) if (v:=z[-1]^(1<<d)) not in z and all((x^v).bit_count()>1 for x in z[:-1])]
    for q in ext:verify(q)
    (r/'novel191.json').write_text(json.dumps({'witness':p,'extensions':ext,'metadata':[g,i]}))
  print(json.dumps([g,i,score,st,classification,p]),file=f);cnt[st]+=1
print(dict(cnt))

