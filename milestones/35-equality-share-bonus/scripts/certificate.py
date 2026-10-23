"""Generate a second, proof-producing encoding of the equality-share test."""
import gzip,json,subprocess,sys,time
from pathlib import Path
from tagged_pair import TaggedPairShare,Cadical153,cycles_of
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
(HERE/'certificates').mkdir(exist_ok=True)
DS=[0,1,2,3,4,1,5];bounds=[(0,21)]*6
e=TaggedPairShare(DS,bounds,11);cuts=[];t=time.monotonic();status='UNKNOWN'
with Cadical153(bootstrap_with=e.clauses) as solver:
 while time.monotonic()-t<120:
  solver.conf_budget(5000);ok=solver.solve_limited()
  if ok is None:continue
  if not ok:status='UNSAT';break
  m=solver.get_model();S=[v for v in e.ball if m[e.var[v]-1]>0];cc=cycles_of(S)
  if not cc:status='SAT';break
  for c in cc:cuts.append(c);e.add([-e.var[v] for v in c],('old',('cut',)));solver.add_clause(e.clauses[-1])
print('Tagged pair',status,'clauses',len(e.clauses),'variables',e.nv,'cuts',len(cuts),flush=True)
(HERE/'data/tagged-screen.json').write_text(json.dumps(dict(status=status,clauses=len(e.clauses),variables=e.nv,cycle_cuts=cuts,seconds=time.monotonic()-t),indent=2)+'\n')
assert status=='UNSAT'
prefix=HERE/'certificates/pairshare';full=prefix.with_suffix('.full.cnf')
full.write_text(f'p cnf {e.nv} {len(e.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses))
CAD=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
def run(cmd,name,code):
 p=subprocess.run(list(map(str,cmd)),capture_output=True,text=True,encoding='utf-8',timeout=300);(HERE/f'logs/{name}.txt').write_text(p.stdout+p.stderr);assert p.returncode==code;return p.stdout
run([CAD,'-q','--no-binary',full,prefix.with_suffix('.drat')],'native-drat',20)
report=run([ROOT/'work/share-wheels/drat-trim.exe',full,prefix.with_suffix('.drat'),'-c',prefix.with_suffix('.core.cnf')],'drat-check',0);assert 's VERIFIED' in report
rawcore=[list(map(int,l.split()))[:-1] for l in prefix.with_suffix('.core.cnf').read_text().splitlines() if l and not l.startswith(('c','p'))]
lookup={tuple(sorted(c)):i for i,c in enumerate(e.clauses)};ids=[lookup[tuple(sorted(c))] for c in rawcore];core=[e.clauses[j] for j in ids]
used=sorted({abs(v) for c in core for v in c});ordering=used+sorted((e.meaning.keys()|e.smeaning.keys())-set(used));rename={v:j+1 for j,v in enumerate(ordering)}
lit=lambda v:(1 if v>0 else -1)*rename[abs(v)]
compact=[[lit(v) for v in c] for c in core]
prefix.with_suffix('.cnf').write_text(f'p cnf {len(used)} {len(compact)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in compact))
run([CAD,'-q','--lrat','--no-binary',prefix.with_suffix('.cnf'),prefix.with_suffix('.lrat')],'native-lrat',20)
meta=dict(module='LocalWindowCnf.PairShare',core_ids=list(range(1,len(core)+1)),source_original_clause_ids=[j+1 for j in ids],active_variables=len(used),original_to_new=rename,dirs=DS,bounds=bounds,joint_cap=9,share_cap=11,cycle_cuts=cuts)
(HERE/'data/pairshare.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Core',len(core),'clauses;',len(used),'variables',flush=True)
