"""Preserve interrupted records and remove only locks with absent owners."""
from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=H/'data/interruption-observation.json';assert not out.exists()
raw=subprocess.check_output(['powershell','-NoProfile','-Command',"@(Get-CimInstance Win32_Process | Where-Object {$_.Name -in @('python.exe','lean.exe','lake.exe','cadical.exe')}|Select-Object ProcessId,ParentProcessId,Name,CommandLine)|ConvertTo-Json -Compress"],text=True).strip()
ps=json.loads(raw or '[]');ps=ps if isinstance(ps,list) else [ps]
oldpids={55632,43492,52152,15392,47988}
assert not any(p['ProcessId'] in oldpids for p in ps),'Original owner still exists; inspect before recovery.'
for p in ps:
 assert not any(s in (p.get('CommandLine') or '') for s in ['129-fourth-count-three/scripts/run_replay.py','129-fourth-count-three\\scripts\\run_replay.py','115-total-count-certificate/scripts/run_batch.py','115-total-count-certificate\\scripts\\run_batch.py','130-fourth-count-large\\scripts\\search.py']),p
dest=H/'audit/interrupted';dest.mkdir(exist_ok=True)
paths=[R/'milestones/129-fourth-count-three/data/replay-progress.json',
 R/'milestones/129-fourth-count-three/data/replay.lock',
 R/'milestones/115-total-count-certificate/data/batch-progress.json',
 R/'milestones/115-total-count-certificate/data/batch.lock',
 R/'milestones/115-total-count-certificate/data/check.lock',H/'data/search.json']
locks=[];rows=[]
for p in paths:
 if p.suffix=='.lock':
  j=json.loads(p.read_text());assert j['pid'] in oldpids
  for k in ['run_record','record']:
   if k in j:paths.append(Path(j[k]))
  locks.append(p)
 name=p.relative_to(R).as_posix();copy=dest/name
 copy.parent.mkdir(parents=True,exist_ok=True);copy.write_bytes(p.read_bytes())
 rows.append(dict(original=name,snapshot=copy.relative_to(H).as_posix(),sha256=sha(copy)))
native=H/'work/large.raw.lrat'
for p in [native,H/'logs/search.stdout.txt',H/'logs/search.stderr.txt']:
 rows.append(dict(original=p.relative_to(R).as_posix(),sha256=sha(p),bytes=p.stat().st_size))
record=dict(status='OBSERVED_INTERRUPTED_OWNERS_ABSENT',observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 processes=ps,missing_owners=sorted(oldpids),preserved=rows,locks_to_remove=[p.relative_to(R).as_posix() for p in locks],
 script_sha256=sha(Path(__file__)),scope='Missing processes establish interruption. Saved RUNNING records do not establish terminal exit status, timeout, or a completed proof. The old native trace and all compiler outputs are retained.')
out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
for p in locks:
 assert p.resolve().is_relative_to(R.resolve()) and p.suffix=='.lock'
 p.unlink()
print(json.dumps(dict(status=record['status'],removed_stale_locks=len(locks),snapshots=len(rows))))
