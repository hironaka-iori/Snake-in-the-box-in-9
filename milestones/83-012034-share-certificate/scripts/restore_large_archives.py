"""Reconstruct split proof archives after checking every part and the final bytes."""
from pathlib import Path
import hashlib,json,os,uuid
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as stream:
        for raw in iter(lambda:stream.read(1024*1024),b''):h.update(raw)
    return h.hexdigest()
saved=json.loads((CASE/'data/pending-checkpoint.json').read_text())
for archive in saved['archives']:
    if 'parts' not in archive:continue
    target=(CASE/archive['path']).resolve();assert target.is_relative_to(CASE.resolve())
    total=hashlib.sha256()
    for part in archive['parts']:
        source=CASE/part['path'];assert source.stat().st_size==part['bytes'] and sha(source)==part['sha256']
        with source.open('rb') as stream:
            for raw in iter(lambda:stream.read(1024*1024),b''):total.update(raw)
    assert total.hexdigest()==archive['sha256']
    if target.exists():assert target.stat().st_size==archive['bytes'] and sha(target)==archive['sha256']
    else:
        temp=target.with_name(target.name+'.'+uuid.uuid4().hex+'.tmp')
        with temp.open('wb') as out:
            for part in archive['parts']:
                with (CASE/part['path']).open('rb') as stream:
                    for raw in iter(lambda:stream.read(1024*1024),b''):out.write(raw)
        assert temp.stat().st_size==archive['bytes'] and sha(temp)==archive['sha256']
        os.replace(temp,target)
print('PASS_SPLIT_ARCHIVE_RESTORATION_OR_EXISTING_BYTES')
