"""Restore exact successful115 records from verified ordered archive parts."""
from pathlib import Path
import hashlib,json,tarfile
H=Path(__file__).resolve().parents[1];R=H.parents[1];S=R/'milestones/115-total-count-certificate'
j=json.loads((H/'data/total115-completion.json').read_text())
def sha(p):
    d=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):d.update(b)
    return d.hexdigest()
archive=H/j['archive']
if not archive.exists():
    pending=archive.with_suffix(archive.suffix+'.restoring')
    with pending.open('xb') as out:
        for row in j['archive_parts']:
            part=H/row['path'];assert sha(part)==row['sha256'] and part.stat().st_size==row['bytes']
            with part.open('rb') as f:
                for b in iter(lambda:f.read(1048576),b''):out.write(b)
    assert sha(pending)==j['archive_sha256'];pending.replace(archive)
assert sha(archive)==j['archive_sha256']
expected={x['path']:x for x in j['archive_members']}
with tarfile.open(archive,'r:gz') as tar:
    for info in tar:
        assert info.isfile();row=expected.pop(info.name)
        dest=(S/info.name).resolve();assert dest.is_relative_to(S.resolve())
        if dest.exists():assert sha(dest)==row['sha256'];continue
        dest.parent.mkdir(parents=True,exist_ok=True)
        pending=dest.with_suffix(dest.suffix+'.restoring')
        with tar.extractfile(info) as f,pending.open('xb') as out:
            for b in iter(lambda:f.read(1048576),b''):out.write(b)
        assert sha(pending)==row['sha256'] and pending.stat().st_size==row['bytes']
        pending.replace(dest)
assert not expected
print('PASS_EXACT_TOTAL115_RECORDS_RESTORED_OR_ALREADY_PRESENT')
