"""Independently replay every positive-hint deduction from original clause identities."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];W=H/'work/conversion-long'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
 d=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
def save(p,j):
 t=p.with_suffix('.tmp');t.write_text(json.dumps(j,indent=2)+'\n');t.replace(p)
c=read(H/'data/conversion-long.json');assert c['status']=='PASS_RUP_ONLY_CONVERSION_DIRECT_REPLAY_PENDING'
assert c['conversion_exit']==0 and c['hints']<=40000000
for p,d in c['source_files_sha256'].items():assert sha(R/p)==d,p
for p,d in c['preserved_files_sha256'].items():assert sha(W/p)==d,p
loc=read(H/'data/native-locate.json');cnf=Path(loc['certificate_files']['cnf']['original'])
raw=cnf.read_text().splitlines();header=raw[0].split();assert header==['p','cnf','11378','92656']
original=[]
for line in raw[1:]:
 if not line or line.startswith('c'):continue
 a=list(map(int,line.split()));assert a[-1]==0 and all(0<abs(v)<=11378 for v in a[:-1]);original.append(tuple(a[:-1]))
assert len(original)==92656
ids=read(W/'core-ids.json');assert ids==sorted(set(ids)) and len(ids)==c['core_clauses']
db={k:original[k-1] for k in ids};used=set();previous=92656;lemmas=hints=0;final_empty=False
gate=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',"$o=Get-CimInstance Win32_OperatingSystem;@{free_bytes=[long]$o.FreePhysicalMemory*1024}|ConvertTo-Json -Compress"],text=True))
assert gate['free_bytes']>=1.5*1024**3
pins={str(p.relative_to(R)):sha(p) for p in [Path(__file__),H/'data/conversion-long.json',H/'data/native-locate.json',H/'data/native-review.json',cnf,W/'trimmed.lrat',W/'core-ids.json']}
record=H/'data/direct-replay.json';assert not record.exists();start=time.monotonic()
j=dict(status='RUNNING_DIRECT_RUP_REPLAY',pid=__import__('os').getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 hint_limit=40000000,time_limit_seconds=180,initial_resources=gate,source_files_sha256=pins,solver_invoked=False,lean_invoked=False)
save(record,j)
try:
 with (W/'trimmed.lrat').open(encoding='ascii') as f:
  for line in f:
   values=list(map(int,line.split()));assert values[-1]==0
   z=values.index(0,1);cid=values[0];clause=values[1:z];hs=values[z+1:-1]
   assert cid>previous and cid not in db and all(0<x<cid for x in hs)
   assert all(0<abs(v)<=11378 for v in clause)
   previous=cid;hints+=len(hs);assert hints<=40000000
   assignments={};conflict=False
   for lit in clause:
    v=abs(lit);value=lit<0
    if v in assignments and assignments[v]!=value:conflict=True
    assignments[v]=value
   for hint in hs:
    assert hint in db,(cid,hint)
    if hint<=92656:used.add(hint)
    if conflict:continue
    units=set();satisfied=False
    for lit in db[hint]:
     v=assignments.get(abs(lit))
     if v is None:units.add(lit)
     elif v==(lit>0):satisfied=True
    assert not satisfied and len(units)<=1,(cid,hint,'nonunit hint')
    if not units:conflict=True
    else:
     unit=next(iter(units));assignments[abs(unit)]=unit>0
   assert conflict,('RUP failed',cid)
   db[cid]=tuple(clause);lemmas+=1;final_empty=not clause
   if lemmas%10000==0:
    assert time.monotonic()-start<=180,'Time limit exceeded'
    j.update(lemmas_checked=lemmas,hints_checked=hints);save(record,j)
 assert final_empty and lemmas==c['lemmas'] and hints==c['hints'] and used==set(ids)
 for p,d in pins.items():assert sha(R/p)==d,p
 j.update(status='PASS_COMPLETE_DIRECT_RUP_REPLAY',final_empty_clause=True,core_inputs_used=len(ids),original_ids_preserved=True,
  every_derived_step_checked=True,all_hint_identities_checked=True)
except BaseException as e:
 j.update(status='FAILED_OR_INCOMPLETE',exception=repr(e));raise
finally:
 j.update(lemmas_checked=lemmas,hints_checked=hints,seconds=time.monotonic()-start,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
  scope='A direct replay of the complete converted Boolean proof. This is independent of the DRAT converter; actual-snake interpretation and Lean checking remain pending.')
 save(record,j);print(json.dumps({k:j.get(k) for k in ['status','lemmas_checked','hints_checked','seconds','final_empty_clause']}),flush=True)
