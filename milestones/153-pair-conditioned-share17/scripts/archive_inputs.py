"""Archive terminal native inputs and complete transport with exact member checks."""
from pathlib import Path
import hashlib,json,zipfile
H=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert read(H/'data/native-queries.json')['queries'][0]['status']=='TIMEOUT'
assert read(H/'critical/data/native-queries.json')['queries'][0]['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
assert read(H/'broader/verification.json')['status']=='PASS_BROADER_CONDITIONS_NATIVE_RUP_REPLAY'
assert read(H/'replay/data/packed-replay.json')['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
groups=[('high-pair-timeout',list((H/'work').rglob('*'))),
        ('critical-certificate',list((H/'critical/work').rglob('*'))),
        ('broader-certificate',[p for p in (H/'broader').rglob('*') if p.name!='verification.json']),
        ('packed-replay',[p for p in (H/'replay/data').rglob('*') if p.suffix in ['.bin','.gz']])]
(H/'archives').mkdir(exist_ok=True);records=[]
for label,paths in groups:
    paths=sorted(p for p in paths if p.is_file());archive=H/'archives'/(label+'153.zip');assert not archive.exists()
    members=[]
    with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for p in paths:
            name=p.relative_to(H).as_posix();z.write(p,name)
            members.append(dict(path=name,bytes=p.stat().st_size,sha256=sha(p)))
    with zipfile.ZipFile(archive) as z:
        assert set(z.namelist())=={x['path'] for x in members}
        for x in members:
            b=z.read(x['path']);assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256']
    records.append(dict(label=label,path=archive.relative_to(H).as_posix(),bytes=archive.stat().st_size,sha256=sha(archive),members=members))
out=dict(status='PASS_BYTE_VERIFIED153_ARCHIVES',archives=records,originals_retained=True,
    total_members=sum(len(x['members']) for x in records),total_archive_bytes=sum(x['bytes'] for x in records),
    scope='One timeout, two complete numerical certificates, and packed transport are distinct. No153 Lean or actual-snake theorem is claimed.')
target=H/'data/archives.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='archives'}))
