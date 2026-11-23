from all_relax import *
def residual():
 z=set()
 for fname in ['routes.log','routes2.log']:
  for s in (D/fname).read_text().splitlines():
   i,st,ng,nd=map(int,s.split())
   if st==0:z.add(i)
 good={int(s.split()[0]) for s in (D/'trims.log').read_text().splitlines() if s.split()[1]=='0'}
 for i,s in enumerate((D/'trims-index.jsonl').read_text().splitlines()):
  if any(k in good for a,n,k in json.loads(s)):z.add(i)
 for s in (D/'allrelax.log').read_text().splitlines():
  i,st,*x=json.loads(s)
  if st in ('UNSAT','CONTAINS'):z.add(i)
 return z
def hit(w,budget):
 n,cla,g=encoding(reconstruct(w));rev={v:k for k,v in g.items()};cands=set(itertools.combinations(g,2));lost=[];cores=[]
 with Cadical195(bootstrap_with=cla) as so:
  start=True;steps=0
  while cands or start:
   pair=() if start else min(cands);start=False
   ass=[-v for k,v in g.items() if k not in pair];so.conf_budget(budget);v=so.solve_limited(assumptions=ass);steps+=1
   if v is True:return 'SAT',steps,list(pair),len(cands),cores
   if v is False:
    cut=tuple(sorted(rev[-x] for x in so.get_core() or ()));assert not set(cut).intersection(pair)
    cores.append(cut);cands={p for p in cands if set(p)&set(cut)};lost=[p for p in lost if set(p)&set(cut)]
   elif pair:lost.append(pair);cands.remove(pair)
  return 'UNKNOWN' if lost else 'UNSAT',steps,lost,len(cands),cores
def go():
 rows=[json.loads(s) for s in (D/'families.jsonl').read_text().splitlines()];done=residual();ids=[i for i in range(len(rows)) if i not in done];print('requested',len(ids),file=sys.stderr,flush=True)
 for i in ids:
  w=rows[i][0];st,n,det,ncan,cores=hit(w,2000)
  print(json.dumps([i,st,n,det,ncan,cores],separators=(',',':')),flush=True)
if __name__=='__main__':go()
