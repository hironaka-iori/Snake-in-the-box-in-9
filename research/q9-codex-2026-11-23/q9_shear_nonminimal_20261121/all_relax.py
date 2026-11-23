from families import *
from relax_encoding import encoding
from pysat.solvers import Cadical195
def atmost(N,cla,g):
 # Direct clauses for at most two absent stretched interiors.
 for u,v,w in itertools.combinations(g,3):cla.append([-u,-v,-w])
 return N,cla
def solve(w,budget):
 N,cla,gates=encoding(reconstruct(w));atmost(N,cla,gates.values())
 with Cadical195(bootstrap_with=cla) as s:
  s.conf_budget(budget);res=s.solve_limited()
  if res:return 'SAT',s.accum_stats()['conflicts'],[i for i,k in gates.items() if k in set(s.get_model())]
  return 'UNSAT' if res is False else 'UNKNOWN',s.accum_stats()['conflicts'],None
def main():
 data=[json.loads(s) for s in (D/'families.jsonl').read_text().splitlines()];limit=int(sys.argv[1]);memo=collections.defaultdict(dict)
 for i,(w,ref) in enumerate(data):
  w=tuple(w);found=None
  for size,table in memo.items():
   for j in range(len(w)-size+1):
    key=sig(w[j:j+size])
    if key in table:found=[j,size,table[key]];break
   if found:break
  if found:print(json.dumps([i,'CONTAINS',found],separators=(',',':')),flush=True);continue
  status,conf,det=solve(w,limit)
  if status=='UNSAT':
   best=w
   for trim in (12,7,4):
    if len(best)<=trim+12:continue
    crop=trim//2;short=best[crop:len(best)-trim+crop]
    few=sum(z.bit_count()>1 for z in short)
    if few>=4 and solve(short,limit//2)[0]=='UNSAT':best=short
   memo[len(best)][sig(best)]=i
   print(json.dumps([i,status,conf,list(best)],separators=(',',':')),flush=True)
  else:print(json.dumps([i,status,conf,det],separators=(',',':')),flush=True)
if __name__=='__main__':main()
