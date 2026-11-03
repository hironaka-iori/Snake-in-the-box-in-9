"""Capture resumable progress and corroborate each driver with its process command."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
raw=subprocess.check_output(['powershell','-NoProfile','-Command',"@(Get-CimInstance Win32_Process | Where-Object {$_.Name -in @('python.exe','lean.exe','lake.exe')} | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"],text=True)
ps=json.loads(raw); ps=ps if isinstance(ps,list) else [ps]
rows=[];stamp=str(time.time_ns())
for folder,file in [('104-complete-potential-batch','batch-progress.json'),('115-total-count-certificate','batch-progress.json'),('122-endpoint-equality','pending-progress.json')]:
 p=R/'milestones'/folder/'data'/file; data=json.loads(p.read_text()); pid=data['pid']
 q=next((x for x in ps if x['ProcessId']==pid),None)
 if q is None:
  assert data['status'].startswith(('PASS_', 'STOPPED')),('Unconfirmed missing driver',folder,pid)
 else:assert folder in q['CommandLine'],('PID reused',folder,pid)
 snap=H/'audit'/('observed-'+folder+'-'+stamp+'.json');snap.write_bytes(p.read_bytes())
 row=dict(batch=folder,pid=pid,process=q,process_live=q is not None,snapshot=snap.relative_to(H).as_posix(),sha256=sha(snap),recorded_status=data['status'])
 if folder.startswith('104'):
  row['selected_modules']=len(data['selected']);row['progress_fields']={k:v for k,v in data.items() if k not in ['selected','modules','checked_modules']}
 elif folder.startswith('115'):
  row['checked_modules']=len(data['checked_modules']);row['total_modules']=data['total_modules']
 lock=R/'milestones'/folder/'data/check.lock'
 if lock.exists():
  lk=json.loads(lock.read_text());rp=Path(lk['run_record']);s=H/'audit'/('observed-'+folder+'-checker-'+stamp+'.json');s.write_bytes(rp.read_bytes())
  row.update(checker_snapshot=s.relative_to(H).as_posix(),checker_snapshot_sha256=sha(s))
  j=json.loads(s.read_text());row['checker_passed_records']=len(j.get('records',[]));row['checker_status']=j.get('status')
 rows.append(row)
out=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),batches=rows,script_sha256=sha(Path(__file__)),scope='Point-in-time process-backed observations only; incomplete batches are not completed proofs.')
p=H/'data/batch-observation.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
for x in rows:print(x['batch'],x['pid'],x.get('checked_modules',x.get('selected_modules',x.get('checker_passed_records'))),flush=True)
