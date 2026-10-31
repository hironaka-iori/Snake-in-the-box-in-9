"""Finite persistent compute batch. No scheduling, privilege changes or unchecked resume."""
from pathlib import Path
import sys,json,time,os,subprocess,argparse,math,hashlib
H=Path(__file__).resolve().parent;D=H/'guarded_runs'
def main():
 p=argparse.ArgumentParser();p.add_argument('--shape',choices=['0120','0123'],required=True);p.add_argument('--rounds',type=int,default=4);p.add_argument('--seconds',type=float,default=120);p.add_argument('--max-proof-steps',type=int,default=400000);a=p.parse_args()
 if a.rounds<0 or not math.isfinite(a.seconds) or a.seconds<=0 or a.max_proof_steps<1:raise ValueError('invalid budget')
 lock=D/f'{a.shape}_batch.lock';statefile=D/f'{a.shape}_batch.json';logfile=D/f'{a.shape}_batch.log'
 with lock.open('x',encoding='utf-8') as f:json.dump({'pid':os.getpid(),'shape':a.shape},f)
 sourcepaths=[H/'continue_guarded.py',H/'cutset_cnf.py']+[H.parent/'branch241-review'/n for n in ['solver.py','solver_plus.py','solver_reduced.py','rup_check.py','alpha_rules_probe.py']]
 sourcehash={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sourcepaths}
 state={'source_hashes':sourcehash,'pid':os.getpid(),'shape':a.shape,'planned_rounds':a.rounds,'seconds_per_round':a.seconds,'max_proof_steps':a.max_proof_steps,'completed':0,'status':'STARTING'}
 def publish():
  temp=statefile.with_suffix('.tmp');temp.write_text(json.dumps(state,indent=2));temp.replace(statefile)
 try:
  publish()
  for j in range(a.rounds):
   if any(hashlib.sha256(Path(p).read_bytes()).hexdigest()!=h for p,h in sourcehash.items()):state['status']='SOURCE_CHANGED';publish();return
   summary=json.loads((D/f'{a.shape}_summary.json').read_text());status=summary['solver']['status'];count=summary['all_RUP']['RUP_steps_checked']
   if status in ['SAT','UNSAT']:state.update(status='TERMINAL_'+status,proof_steps=count);publish();return
   if count>=a.max_proof_steps:state.update(status='CHECKPOINT_LIMIT',proof_steps=count);publish();return
   strategy='luby' if j%2==0 else 'lbd';state.update(status='RUNNING',batch_round=j+1,strategy=strategy,proof_steps_before=count);publish()
   with logfile.open('a',encoding='utf-8') as f:
    code=subprocess.call([sys.executable,str(H/'continue_guarded.py'),'--shape',a.shape,'--seconds',str(a.seconds),'--restart',strategy,'--batch-pid',str(os.getpid())],stdout=f,stderr=subprocess.STDOUT)
   if code:state.update(status='FAILED',return_code=code);publish();return
   state['completed']=j+1
   latest=json.loads((D/f'{a.shape}_summary.json').read_text());state['proof_steps']=latest['all_RUP']['RUP_steps_checked']
   if latest['solver']['status'] in ['SAT','UNSAT']:state['status']='TERMINAL_'+latest['solver']['status'];publish();return
   publish()
  state['status']='BUDGET_EXHAUSTED';publish()
 except Exception as exc:
  state.update(status='FAILED',error=str(exc));publish();raise
 finally:lock.unlink()
if __name__=='__main__':main()
