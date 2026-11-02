"""Verify frozen evidence and exact indexed bytes without disturbing a live replay."""
from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checkpoint=read(HERE/'data/checkpoint.json')
assert len(checkpoint['new_theorem_audits'])==39
snapshot=HERE/'replay-snapshot/record.json';assert sha(snapshot)==checkpoint['replay_snapshot_sha256']
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7305'
for row in read(snapshot)['records']:
    assert sha(CASE/'lean'/(row['module']+'.lean'))==row['source_sha256']
    assert sha(HERE/row['snapshot_log'])==row['log_sha256']
for row in read(HERE/'data/repository-check.json')['files']:
    assert sha(HERE/row['snapshot'])==row['sha256']
raw=subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','--stage','-z','--',HERE.relative_to(ROOT).as_posix()],cwd=ROOT)
checked=[]
for line in raw.decode().split('\0'):
    if not line:continue
    metadata,relative=line.split('\t',1);_,oid,stage=metadata.split();assert stage=='0'
    path=ROOT/relative
    if path.name=='staged-evidence.json' or path.suffix not in ['.lean','.json','.log','.py']:continue
    data=path.read_bytes();actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert actual==oid,'Git changed audited bytes: '+relative
    checked.append(relative)
assert checked,'Stage this milestone before verifying indexed bytes'
out=dict(status='PASS_SAVED_MILESTONE75_AND_STAGED_BYTES',indexed_files=len(checked),files=checked,
         checkpoint_sha256=sha(HERE/'data/checkpoint.json'),scope='Saved successful proof/snapshot provenance and exact indexed bytes. Live completion records may advance independently; no new global theorem.')
(HERE/'data/staged-evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(checked),'files')
