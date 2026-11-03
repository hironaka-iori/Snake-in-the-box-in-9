"""Archive the exact complete generated replay sources after the first group passes."""
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
assert read(H/'data/first-group-completion.json')['status']=='PASS_FIRST32_REPLAY_SEGMENTS_AND_CHECKPOINT'
plan=read(H/'data/full-source-plan.json');assert plan['module_count']==342
paths=[]
for a in plan['artifacts']:
    p=H/a['path'];assert sha(p)==a['sha256'];paths.append(p)
assert len(set(paths))==342
out=H/'archives';out.mkdir(exist_ok=True);groups=[];group=[];size=0
for p in sorted(paths):
    n=p.stat().st_size;assert n<85000000
    if group and size+n>85000000:groups.append(group);group=[];size=0
    group.append(p);size+=n
if group:groups.append(group)
archives=[]
for i,ps in enumerate(groups):
    target=out/f'sources151-part{i:02d}.zip';assert not target.exists()
    members=[]
    with zipfile.ZipFile(target,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for p in ps:
            name=p.relative_to(R).as_posix();d=sha(p);n=p.stat().st_size
            z.write(p,name);members.append(dict(path=name,bytes=n,sha256=d))
    assert target.stat().st_size<100000000
    with zipfile.ZipFile(target) as z:
        assert z.namelist()==[m['path'] for m in members]
        for m in members:
            with z.open(m['path']) as f:assert digest(f)==m['sha256']
    archives.append(dict(path=target.relative_to(R).as_posix(),bytes=target.stat().st_size,sha256=sha(target),members=members))
    print('ARCHIVED',i,len(members),target.stat().st_size,flush=True)
record=dict(status='PASS_BYTE_VERIFIED_FULL_SOURCE_ARCHIVE',archives=archives,
    member_count=342,total_original_bytes=sum(p.stat().st_size for p in paths),
    original_files_retained=True,accepted_modules=49,complete_Lean_replay=False,
    scope='Every generated source is preserved exactly.49 modules are accepted; the remaining293 and the actual-snake composition are uncompleted.')
(H/'data/source-archives.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(record['status'])
