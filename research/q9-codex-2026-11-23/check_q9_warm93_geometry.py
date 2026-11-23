import json,gzip,sys
from split_q9_long_donor_ports import path,run
from search_q9_donor_port_branches import branch
from itertools import product
from concurrent.futures import ProcessPoolExecutor
def work(t):
 w,ep=t;p=path(w);full=[2,0] if ep==0 else [0,2]
 delta=sum((-1)**v.bit_count() for v in p)-(full[0]-full[1])//2
 ports=tuple(sorted((p[0],p[-1])))
 r=run((w,((),ports,full,full,delta),20))
 if r.get("empty"):return [w,ep,"EMPTY",0,None],r
 s,n,hit=branch(r,192,3000000)
 return [w,ep,s,n,hit],r
if __name__=="__main__":
 a=[json.loads(l)[1] for l in open("q9_warm93_free_tails.jsonl") if l.startswith("[")]
 with gzip.open("q9_warm93_exact_duals.jsonl.gz","wt") as out,ProcessPoolExecutor(2) as pool:
  for z,r in pool.map(work,[(w,e) for w in sorted({v['word'] for v in a}) for e in (0,1)]):
   print(json.dumps(r,separators=(",",":")),file=out);out.flush()
   print(json.dumps(z,separators=(",",":")),flush=True)

