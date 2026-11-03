"""Record that incomplete replay cannot trigger either acceptance stage."""
from pathlib import Path
import hashlib, json, subprocess, sys
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
P=R/'milestones/151-countfree-replay-pilot'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert read(P/'data/full-replay-progress.json')['status']=='RUNNING'
targets=[H/'data/replay-completion.json', H/'data/ShareComplete152-audit.json', H/'build/ShareComplete152.olean']
assert all(not p.exists() for p in targets)
checks=[]
for name,args in [('audit_full.py',[]),('check_complete.py',['ShareComplete152'])]:
    p=H/'scripts'/name
    result=subprocess.run([sys.executable,'-B','-X','utf8',str(p),*args],cwd=R,capture_output=True,text=True)
    out=json.loads(result.stdout)
    assert result.returncode==2 and out['status']=='WAITING_FOR_COMPLETE_REPLAY'
    assert not result.stderr
    checks.append(dict(script=name,sha256=sha(p),exit_code=result.returncode,output=out))
assert all(not p.exists() for p in targets)
record=dict(status='PASS_INCOMPLETE_REPLAY_REJECTED',checks=checks,no_acceptance_artifact_created=True)
dest=H/'data/pending-guard-tests.json';assert not dest.exists()
dest.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
controller=H/'scripts/serialize_complete.py'
snapshot=H/'audit/active-controller.exact.py';snapshot.parent.mkdir(exist_ok=True);assert not snapshot.exists()
snapshot.write_bytes(controller.read_bytes())
record['controller_sha256']=sha(controller)
print(json.dumps(record))
