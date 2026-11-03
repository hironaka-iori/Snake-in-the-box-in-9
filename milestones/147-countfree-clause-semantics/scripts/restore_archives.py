"""Verify archived paths and hashes; restore missing files without overwriting."""
from pathlib import Path,PurePosixPath
import hashlib,json,zipfile
P=Path(__file__).resolve().parents[1];R=P.parents[1].resolve()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def digest(f):
    h=hashlib.sha256()
    for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def sha(p):
    with p.open('rb') as f:return digest(f)
j=read(P/'data/replay-archives.json');assert j['status']=='PASS_BYTE_VERIFIED_REPLAY_ARCHIVES'
restored=0
for a in j['archives']:
    ap=(R/a['path']).resolve();assert ap.is_relative_to(P.resolve())
    assert sha(ap)==a['sha256'] and ap.stat().st_size==a['bytes']
    with zipfile.ZipFile(ap) as z:
        assert z.namelist()==[x['path'] for x in a['members']]
        for x in a['members']:
            relative=PurePosixPath(x['path'])
            assert not relative.is_absolute() and '..' not in relative.parts
            dest=(R/relative).resolve();assert dest.is_relative_to((P/'replay').resolve())
            with z.open(x['path']) as f:assert digest(f)==x['sha256']
            if dest.exists():assert sha(dest)==x['sha256'] and dest.stat().st_size==x['bytes']
            else:
                dest.parent.mkdir(parents=True,exist_ok=True)
                with z.open(x['path']) as f,dest.open('xb') as out:
                    for b in iter(lambda:f.read(1048576),b''):out.write(b)
                assert sha(dest)==x['sha256'] and dest.stat().st_size==x['bytes'];restored+=1
print(json.dumps(dict(status='PASS_EXACT_REPLAY_ARCHIVE_RESTORE',restored=restored)))
