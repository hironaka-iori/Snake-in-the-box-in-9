"""Seek a smaller proof from the already-refuted tagged core; preserve the first proof."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=read(H/'data/trimmed-certificate.json');cnf=H/'work/core.cnf'
assert sha(cnf)==old['core_sha256']
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
raw=H/'work/core-unsat.raw.lrat';trim=H/'work/core-unsat.trim.lrat';record=H/'data/core-search.json'
so=H/'logs/core-search.stdout.txt';se=H/'logs/core-search.stderr.txt'
assert not any(p.exists() for p in [raw,trim,record,so,se])
cmd=[str(exe),'-q','--unsat','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
out=dict(status='RUNNING',command=cmd,timeout_seconds=180,cnf_sha256=sha(cnf),prior_certificate_sha256=sha(H/'data/trimmed-certificate.json'),
 solver_sha256=sha(exe),script_sha256=sha(Path(__file__)),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
def save():record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();start=time.monotonic()
with so.open('wb') as stdout,se.open('wb') as stderr:
 proc=subprocess.Popen(cmd,stdout=stdout,stderr=stderr);out['pid']=proc.pid;save()
 try:
  code=proc.wait(timeout=180)
  out.update(exit_code=code,status='NATIVE_UNSAT_CORE_PROOF_PENDING' if code==20 and b's UNSATISFIABLE' in so.read_bytes() else 'FAILED')
 except subprocess.TimeoutExpired:
  proc.kill();proc.wait(timeout=15);out.update(exit_code=proc.returncode,status='TIMEOUT')
out.update(seconds=time.monotonic()-start,raw_sha256=sha(raw),raw_bytes=raw.stat().st_size,stdout_sha256=sha(so),stderr_sha256=sha(se));save()
if out['status']!='NATIVE_UNSAT_CORE_PROOF_PENDING':print(json.dumps(out,indent=2));sys.exit(0)
sys.dont_write_bytecode=True
generator=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
assert sha(generator)==old['trimming_generator_sha256']
sp=importlib.util.spec_from_file_location('core129',generator);g=importlib.util.module_from_spec(sp);sp.loader.exec_module(g)
nl,nh,ids=g.trim_lrat(str(raw),str(trim),old['core_clauses'])
mapped=H/'work/core-unsat.mapped.lrat';N=old['core_clauses']
def cid(i):return old['core_ids'][i-1] if i<=N else 112225+i-N
active=set();maxh=maxcl=0
full=[[int(x) for x in s.split()[:-1]] for s in (H/'work/expanded.cnf').read_text().splitlines()[1:]]
globalids=[old['core_ids'][i-1] for i in ids]
for i in globalids:active.update(abs(x) for x in full[i-1]);maxcl=max(maxcl,len(full[i-1]))
with mapped.open('x',encoding='ascii',newline='\n') as dst,trim.open() as src:
 for line in src:
  row=list(map(int,line.split()));z=row.index(0,1);cl=row[1:z];hs=row[z+1:-1]
  assert row[-1]==0 and row[0]>N and all(0<h<row[0] for h in hs)
  active.update(abs(x) for x in cl);maxh=max(maxh,len(hs));maxcl=max(maxcl,len(cl))
  dst.write(' '.join(map(str,[cid(row[0]),*cl,0,*[cid(h) for h in hs],0]))+'\n')
assert not cl
smaller=H/'work/selected-core.cnf'
smaller.write_bytes((f'p cnf 10175 {len(globalids)}\n'+''.join(' '.join(map(str,full[i-1]))+' 0\n' for i in globalids)).encode())
out.update(status='CORE_PROOF_TRIMMED_REPLAY_PENDING',lemmas=nl,hints=nh,core_clauses=len(ids),core_ids=globalids,
 active_variables=len(active),active_variable_ids=sorted(active),max_clause_length=maxcl,max_step_hints=maxh,
 trimmed_sha256=sha(trim),mapped_sha256=sha(mapped),selected_core_sha256=sha(smaller),
 scope='A new proof of a subset of the same tagged inputs. Local input IDs map to saved original core IDs. Full replay and Lean actual-snake interpretation remain required.')
save();print(json.dumps({k:v for k,v in out.items() if k not in ['core_ids','active_variable_ids']},indent=2))
