from wide import get_refs
from prepare import *
from end_encoding import encoding
from pysat.card import CardEnc,EncType
from pysat.solvers import Cadical195
from concurrent.futures import ProcessPoolExecutor
def work(job):
 i,ref,budget=job;r=ref[0];c=r['p'];N,cla,gd=encoding(c,r['L'],r['R'],r['rem']);g=list(gd.values());k=1 if r['label'][1:4]=='190' else 2
 ca=CardEnc.equals(g,k,top_id=N,encoding=EncType.seqcounter)
 with Cadical195(bootstrap_with=cla+ca.clauses) as s:
  s.conf_budget(budget);res=s.solve_limited();ans='SAT' if res else 'UNSAT' if res is False else 'UNKNOWN'
  model=set(s.get_model()) if res else set()
  return [i,ans,s.accum_stats()['conflicts'],[j for j,x in gd.items() if x in model],[[a['label'],a['ix']] for a in ref]]
def main():
 op=json.loads((D/'motif.json').read_text())['open'];families=[json.loads(s) for s in (D/'families.jsonl').read_text().splitlines()];refs=get_refs();groups={}
 for i in op:
  for ff,ix in families[i][1]:
   c=refs[ff,ix];k=(1 if ff[1:4]=='190' else 2,c['rem'],key(c));groups.setdefault(k,[]).append(c)
 jobs=[(i,r,35000) for i,r in enumerate(groups.values())]
 with ProcessPoolExecutor(2) as pool:
  for r in pool.map(work,jobs):print(json.dumps(r,separators=(',',':')),flush=True)
if __name__=='__main__':main()
