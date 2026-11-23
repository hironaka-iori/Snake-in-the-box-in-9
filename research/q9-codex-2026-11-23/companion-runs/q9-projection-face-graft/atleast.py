from run import *
g=int(sys.argv[1]);budget=int(sys.argv[2]);second=len(sys.argv)>3
bank=[list(map(int,s.split()))[3:] for s in (r/'parents.pts').open()];rows=[list(map(int,s.split())) for s in (r/('exact.pts' if g else 'grafts.pts')).open()]
def bitset(p):return sum(1<<x for x in {z%256 for z in p})
base=[bitset(p) for p in bank]
def coltag(a,b,m,v):
 F=sum(1<<x for x in range(v,256) if (x&m)==v);return (base[a]&~F)|(base[b]&F)
seen=set()
if g:
 for s in (r/'grafts.pts').open():
  a,b,m,v,*_=map(int,s.split());seen.add(coltag(a,b,m,v))
pre=r/f'ge{g}.jsonl';inc=list(range(len(rows))) if not second else [json.loads(l)[0] for l in pre.open() if json.loads(l)[1]=='UNKNOWN'];rng=random.Random(91+g);rng.shuffle(inc);counts=Counter()
with (r/(f'ge{g}retry.jsonl' if second else f'ge{g}.jsonl')).open('w',1) as out:
 for i in inc:
  a,b,m,v,*_=rows[i];key=coltag(a,b,m,v)
  if key in seen:continue
  seen.add(key);h=combine(bank[a],bank[b],m,v);sf=combine(bank[a],bank[b],m,v,True)
  if len(h^set(bank[a]))>len(sf^set(bank[a])):h=sf
  st,p=solve(h,192,budget,atleast=True)
  if p:
   verify(p);assert len(p)>=193 and bitset(p)==key
  counts[st]+=1;print(json.dumps([i,st,p]),file=out)
  if p:break
print(g,dict(counts))

