"""Restore exact missing archived inputs beneath this repository; never replace differing files."""
from pathlib import Path
import hashlib,json,zipfile
H=Path(__file__).resolve().parents[1];R=H.parents[1].resolve()
def digest(f):
    d=hashlib.sha256()
    for b in iter(lambda:f.read(1048576),b''):d.update(b)
    return d.hexdigest()
def sha(p):
    with p.open('rb') as f:return digest(f)
j=json.loads((H/'data/source-archives.json').read_text(encoding='utf-8-sig'))
assert j['status']=='PASS_BYTE_VERIFIED_FULL_SOURCE_ARCHIVE'
restored=0;existing=0
for a in j['archives']:
    p=R/a['path'];assert sha(p)==a['sha256']
    with zipfile.ZipFile(p) as z:
        assert z.namelist()==[m['path'] for m in a['members']]
        for m in a['members']:
            target=(R/m['path']).resolve();assert target.is_relative_to(R)
            with z.open(m['path']) as f:assert digest(f)==m['sha256']
            if target.exists():
                assert target.is_file() and sha(target)==m['sha256'],target
                existing+=1;continue
            target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as f,z.open(m['path']) as src:
                for b in iter(lambda:src.read(1048576),b''):f.write(b)
            assert sha(target)==m['sha256'];restored+=1
print(json.dumps(dict(status='PASS_EXACT_RESTORATION',restored=restored,existing_verified=existing)))
