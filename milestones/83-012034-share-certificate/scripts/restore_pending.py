"""Restore archived pending sources and proof bytes without replacing different files."""
from pathlib import Path
import hashlib,json,runpy,tarfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
runpy.run_path(str(HERE/'scripts/restore_large_archives.py'))
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
pending=read(CASE/'data/pending-checkpoint.json');selection=read(CASE/'data/lrat-slice-selection.json')
backup=(CASE/selection['backup_manifest']).parent
for archive in pending['archives']:
    path=CASE/archive['path'];assert sha(path.read_bytes())==archive['sha256']
    base=backup if path.name=='original-proof-evidence.tar.gz' else CASE
    found={}
    with tarfile.open(path,'r:gz') as tf:
        for member in tf:
            assert member.isfile() and not member.issym() and not member.islnk()
            assert not Path(member.name).is_absolute() and '..' not in Path(member.name).parts
            target=(base/member.name).resolve();assert target.is_relative_to(CASE.resolve())
            assert member.name not in found
            raw=tf.extractfile(member).read();digest=sha(raw)
            assert digest==archive['members'][member.name]
            if target.exists():assert sha(target.read_bytes())==digest,str(target)
            else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
            found[member.name]=digest
    assert found==archive['members']
print('PASS_PENDING_SOURCE_AND_PROOF_RESTORATION_OR_EXISTING_BYTES')
