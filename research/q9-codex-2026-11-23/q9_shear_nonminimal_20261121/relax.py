from prepare import *
from relax_encoding import encoding
from pysat.solvers import Cadical195
from pysat.card import CardEnc,EncType
def work(p,limit=8,budget=100000):
 n,cla,gd=encoding(p);g=list(gd.values());assert g
 counts=[];omits=[]
 for k in (1,2):
  card=CardEnc.equals(g,k,top_id=n,encoding=EncType.seqcounter)
  with Cadical195(bootstrap_with=cla+card.clauses) as s:
   st=None
   for it in range(limit+1):
    s.conf_budget(budget);res=s.solve_limited()
    if res is not True:st='UNSAT' if res is False else 'UNKNOWN';break
    mod=set(s.get_model());sel=[i for i,j in gd.items() if j in mod];assert len(sel)==k
    if it==limit:st='CAPPED';break
    omits.append(sel);s.add_clause([-gd[i] for i in sel])
   counts.append([k,st,it,s.accum_stats()['conflicts']])
 return counts,omits
if __name__=='__main__':
 for i,line in enumerate((D/'cases.jsonl').read_text().splitlines()):
  r=json.loads(line);z=work(r['p']);print(json.dumps([i,*z],separators=(',',':')),flush=True)
