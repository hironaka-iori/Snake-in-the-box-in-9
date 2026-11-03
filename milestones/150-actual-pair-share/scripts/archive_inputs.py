"""Archive completed native inputs and packed transport; preserve originals."""
from pathlib import Path
import hashlib,json,zipfile
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def digest(f):
    d=hashlib.sha256()
    for b in iter(lambda:f.read(1048576),b''):d.update(b)
    return d.hexdigest()
def sha(p):
    with p.open('rb') as f:return digest(f)
assert read(H/'data/native-queries.json')['status']=='BOUNDED_NATIVE_QUERIES_FINISHED'
transport=read(H/'replay/data/packed-replay.json')
assert transport['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
paths=set(p for p in (H/'work').rglob('*') if p.is_file())
for item in transport['artifacts']+transport['checkpoints']:
    p=H/'replay'/item['path'];assert sha(p)==item['sha256'];paths.add(p)
out=H/'archives';out.mkdir(exist_ok=True)
groups=[];group=[];size=0
for p in sorted(paths):
    n=p.stat().st_size;assert n<85000000,p
    if group and size+n>85000000:groups.append(group);group=[];size=0
    group.append(p);size+=n
if group:groups.append(group)
archives=[]
for i,ps in enumerate(groups):
    target=out/f'inputs150-part{i:02d}.zip';assert not target.exists()
    members=[]
    with zipfile.ZipFile(target,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for p in ps:
            name=p.relative_to(R).as_posix();d=sha(p);n=p.stat().st_size
            z.write(p,name);members.append(dict(path=name,bytes=n,sha256=d))
    assert target.stat().st_size<100000000
    with zipfile.ZipFile(target) as z:
        assert z.namelist()==[m['path'] for m in members]
        for m in members:
            assert z.getinfo(m['path']).file_size==m['bytes']
            with z.open(m['path']) as f:assert digest(f)==m['sha256'],m['path']
    archives.append(dict(path=target.relative_to(R).as_posix(),bytes=target.stat().st_size,
                         sha256=sha(target),members=members))
    print('ARCHIVED',i,len(members),target.stat().st_size,flush=True)
record=dict(status='PASS_BYTE_VERIFIED_NATIVE_AND_TRANSPORT_ARCHIVES',archives=archives,
    member_count=len(paths),total_original_bytes=sum(p.stat().st_size for p in paths),
    original_files_retained=True,lean_replay_complete=False,
    scope='Native solver evidence, complete numerical replay and packed transport. Lean acceptance is separate.')
(H/'data/input-archives.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(record['status'],flush=True)
