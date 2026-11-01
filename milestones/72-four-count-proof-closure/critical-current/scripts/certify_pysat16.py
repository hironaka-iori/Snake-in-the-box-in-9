"""Alternative proof-producing backend for the unresolved share-16 windows."""
from pathlib import Path
from collections import Counter
import hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import Cadical153,census,window
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import gen_lean_sat as gen
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
index=int(sys.argv[1]);seconds=float(sys.argv[2]) if len(sys.argv)>2 else 60
cap=int(sys.argv[3]) if len(sys.argv)>3 else 15
ds=read(HERE/'data/all-six-direction-shapes.json')['up_to_reversal'][index]
cuts=read(HERE/'data/cap15-cyclic-control.json')['cycles'] if index==3 else []
enc=TaggedShare(ds,[(0,21)]*5,cap)
for c in cuts:
 assert gen.is_cycle_set(c);enc.add([-enc.var[v] for v in c],('old',('cut',)))
prefix=HERE/f'build/pysat{index}-cap{cap}';cnf=prefix.with_suffix('.cnf');drat=prefix.with_suffix('.drat');core=prefix.with_suffix('.core.cnf')
cnf.write_text(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses))
start=time.monotonic();ok=None;S=None
with Cadical153(bootstrap_with=enc.clauses,with_proof=True) as solver:
 while ok is None and time.monotonic()-start<seconds:
  solver.conf_budget(10000);ok=solver.solve_limited()
 if ok is False:drat.write_text('\n'.join(solver.get_proof())+'\n')
 elif ok is True:
  model=solver.get_model();S={v for v in enc.ball if model[enc.var[v]-1]>0}
out=dict(shape_index=index,directions=ds,bounds=[(0,21)]*5,cap=cap,cycle_cuts=cuts,solver='PySAT Cadical153 proof mode',seconds=time.monotonic()-start,requested_seconds=seconds,cnf_sha256=sha(cnf),status='UNKNOWN',scope='Solver result only until independent DRAT verification; geometric interpretation and Lean replay remain separate.')
if ok is False:
 out['drat_sha256']=sha(drat)
 try:
  r=subprocess.run([str(ROOT/'work/share-wheels/drat-trim.exe'),str(cnf),str(drat),'-c',str(core)],capture_output=True,text=True,timeout=60)
  (HERE/f'logs/pysat{index}-cap{cap}-verify.log').write_text(r.stdout+r.stderr)
  out['verify_exit']=r.returncode
  if r.returncode==0 and 's VERIFIED' in r.stdout:
   lookup={tuple(sorted(c)):tag for c,tag in zip(enc.clauses,enc.tags)}
   tags=[lookup[tuple(sorted(map(int,l.split()[:-1])))][0] for l in core.read_text().splitlines() if l and l[0] not in 'pc']
   out.update(status='NATIVE_DRAT_VERIFIED',core_sha256=sha(core),core_clause_tags=dict(Counter(tags)))
  else:out['status']='DRAT_VERIFY_FAILED'
 except subprocess.TimeoutExpired:out['status']='DRAT_VERIFY_TIMEOUT'
elif S is not None:
 report=census(S,9,window(ds)[1:-1]);report.pop('degree');out.update(status='SAT_LOCAL_RELAXATION',selected=sorted(S),census=report)
(HERE/f'data/pysat{index}-cap{cap}-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['cycle_cuts','selected','census']},flush=True)
