"""Bounded pure-Python probes of the actual project window CNF.
All SAT models checked against clauses; all learned RUP hints checked independently.
UNKNOWN means only that a finite budget expired. No numerical a(9) claim.
"""
import argparse,gzip,hashlib,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent;BASE=HERE.parent/'branch241-next';sys.path[:0]=[str(BASE),str(BASE/'encoding')]
from github_query import build,REPO
from charge_fast import Geometry,Charges
from solver import Solver
from rup_check import check

def run(k,cap,seconds,out):
 bank=json.loads((REPO/'work/bank9.json').read_text());path=bank[67]['vertex_sequence'][:k+2];E,geo,m,meta=build(path,cap);cs=[c[:] for c in E.cnf.clauses]
 s=Solver(cs,E.cnf.nv,primary=E.var.values(),phase_true=E.var.values());r=s.solve(seconds=seconds)
 proofcheck=check(cs,s.proof,require_empty=r['status']=='UNSAT')
 model=r.pop('model',None)
 if model is not None:
  a={abs(l):l>0 for l in model};assert all(any(a[abs(l)]==(l>0) for l in c) for c in cs)
  selected=[v for v,x in E.var.items() if a[x]];cost=Charges(Geometry(9),selected).cheap()['r6plus'];assert sum(cost['values'][x] for x in E.centres)<=cap
  r['selection']=selected;r['warning']='Necessary-condition local model, not automatically a genuine global snake.'
 out.mkdir(parents=True,exist_ok=True);tag=f'k{k}_cap{cap}';payload={'clauses':cs,'variables':E.cnf.nv,'proof':s.proof,'meta':meta,'result':r}
 with gzip.open(out/(tag+'.json.gz'),'wt',encoding='utf-8') as f:json.dump(payload,f,separators=(',',':'))
 r.update(centres=k,cap=cap,proof_check=proofcheck,artifact=tag+'.json.gz',CNF_sha256=hashlib.sha256(json.dumps(cs,separators=(',',':')).encode()).hexdigest())
 (out/(tag+'_result.json')).write_text(json.dumps(r,indent=2));print(json.dumps({a:b for a,b in r.items() if a!='selection'}),flush=True);return r

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--centres',type=int,default=1);ap.add_argument('--caps',type=int,nargs='+',default=[0,21,42,63,84]);ap.add_argument('--seconds',type=float,default=5);ap.add_argument('--out',type=Path,default=HERE/'probes');args=ap.parse_args()
 rows=[run(args.centres,c,args.seconds,args.out) for c in args.caps];(args.out/'summary.json').write_text(json.dumps(rows,indent=2))
if __name__=='__main__':main()
