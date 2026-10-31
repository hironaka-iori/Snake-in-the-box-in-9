"""Merge independently RUP-checked portfolio tails by exact clause-ID translation.
Never concatenate unshifted hints; original CNF and frozen prefix must match.
"""
from pathlib import Path
import json,gzip,hashlib,argparse
from rup_check import check
from research_loop import save
from benchmark_portfolio import CONFIGS
H=Path(__file__).resolve().parent;O=H/'portfolio_results'
def merge(shape,overwrite=False):
 if (O/f"merged_{shape}.json.gz").exists() and not overwrite:raise FileExistsError("merged checkpoint exists; use continue, or explicitly --overwrite after preserving it")
 with gzip.open(H/f'alpha_rules_d{shape}/experiment.json.gz','rt') as f:d=json.load(f)
 cs=d['clauses'];prefix=d['proof'];n=len(cs)+len(prefix);frozen=cs+[p['clause'] for p in prefix];digest=hashlib.sha256(json.dumps(cs,separators=(',',':')).encode()).hexdigest();combined=prefix[:];offset=0;reports=[]
 for name in CONFIGS:
  with gzip.open(O/f'{shape}_{name}.json.gz','rt') as f:t=json.load(f)
  assert t['summary']['source_CNF_sha256']==digest and t['summary']['frozen_prefix_steps']==len(prefix)
  if 'frozen_prefix_sha256' in t['summary']:assert t['summary']['frozen_prefix_sha256']==hashlib.sha256(json.dumps(prefix,separators=(',',':')).encode()).hexdigest()
  check(frozen,t['proof_tail'],require_empty=t['summary']['solver']['status']=='UNSAT')
  tail=[{'clause':p['clause'],'hints':[i if i<=n else i+offset for i in p['hints']]} for p in t['proof_tail']]
  combined.extend(tail);offset+=len(tail);reports.append({'configuration':name,'steps':len(tail)})
  empty=next((i for i,p in enumerate(combined) if not p['clause']),None)
  if empty is not None:
   combined=combined[:empty+1];break
 result=check(cs,combined,require_empty=False)
 save(O/f'merged_{shape}.json.gz',{'clauses':cs,'proof':combined,'meta':d['meta'],'phase_true':d.get('phase_true',[]),'merge_report':reports,'checked':result,'round':0})
 print(json.dumps({'shape':shape,'merged_new_steps':offset,'complete_checked':result}),flush=True)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--overwrite',action='store_true');args=ap.parse_args()
 for s in ['0120','0123']:merge(s,args.overwrite)
