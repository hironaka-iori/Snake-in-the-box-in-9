"""Retain the mathematical acceptance checks and replace the obsolete hold check."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
p=H/'scripts/audit_actual.py';s=p.read_text(encoding='utf-8')
before="""guards=list((H/'data').glob('serialization-final-*.json'))
assert len(guards)==1
guard=read(guards[0]); assert guard['status']=='RESUMED' and guard['resume_return_code']==0 and guard['transfer_exit_code']==0"""
after="""recovery_path=H/'data/reboot-recovery-v2-progress.json'
recovery=read(recovery_path)
assert recovery['status']=='PASS_RECOVERED_ACTUAL_SNAKE_COMPOSITION'
assert recovery['previous_processes_confirmed_absent']
assert recovery['final_receipt_sha256']==sha(final_path)
assert [Path(x['script']).name for x in recovery['stages']]==['run_full_replay.py','audit_full.py','check_complete.py']
for stage in recovery['stages']:
    assert stage['exit_code']==0 and sha(stage['log'])==stage['log_sha256']
for path,digest in recovery['pins'].items():assert sha(path)==digest,path
for row in recovery['historical_records']:assert sha(row['archive'])==row['sha256']
# No held coordinator survived the reboot. A RESUMED receipt would be false.
guards=[recovery_path]"""
assert s.count(before)==1
s=s.replace(before,after)
s=s.replace("scope='The local share16 theorem is complete.","recovered_after_reboot=True,\n    scope='The local share16 theorem is complete.")
q=H/'scripts/audit_actual_after_reboot.py';assert not q.exists()
q.write_text(s,encoding='utf-8',newline='\n')
out=dict(status='PREPARED_REBOOT_AWARE_FINAL_AUDIT',
    original_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
    successor_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),
    change='Only the process serialization evidence is replaced by verified reboot recovery. All mathematical receipts, source, object, dependencies, theorem and axiom checks are preserved.')
(H/'data/recovery-audit-preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
