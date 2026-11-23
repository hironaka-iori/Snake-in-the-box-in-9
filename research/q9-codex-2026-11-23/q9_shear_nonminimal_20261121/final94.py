from hitting import *
from pysat.card import CardEnc,EncType
from concurrent.futures import ProcessPoolExecutor
def one(x):
 i,w=x;n,cla,g=encoding(reconstruct(w));ks=list(g.values());card=CardEnc.equals(ks,2,top_id=n,encoding=EncType.seqcounter)
 # Once an interior is omitted, all its variables can be set false. A full embedding
 # extends to this restricted relaxation by retaining exactly the unomitted routes.
 with Cadical195(bootstrap_with=cla+card.clauses) as s:
  s.conf_budget(140000);res=s.solve_limited()
  v=set(s.get_model() or ()) if res else set()
  return [i,('SAT' if res else 'UNSAT' if res is False else 'UNKNOWN'),s.accum_stats()['conflicts'],[j for j,k in g.items() if k in v]]
if __name__=='__main__':
 rows=[json.loads(s) for s in (D/'families.jsonl').read_text().splitlines()]
 jobs=[(i,rows[i][0]) for i in sorted(set(range(len(rows)))-residual())]
 with ProcessPoolExecutor(2) as ex:
  for res in ex.map(one,jobs,chunksize=1):print(json.dumps(res,separators=(',',':')),flush=True)
