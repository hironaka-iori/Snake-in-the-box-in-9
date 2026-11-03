"""Archive immutable large replay material, verify every restored byte, keep originals."""
from pathlib import Path
import hashlib,json,zipfile
P=Path(__file__).resolve().parents[1];H=P/'replay';R=P.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def digest(stream):
    h=hashlib.sha256()
    for b in iter(lambda:stream.read(1048576),b''):h.update(b)
    return h.hexdigest()
def sha(p):
    with p.open('rb') as f:return digest(f)
full=read(H/'data/full-source-plan.json');native=read(H/'data/packed-replay.json')
paths={H/x['path'] for x in full['artifacts']+native['artifacts']+native['checkpoints']}
paths.add(H/'data/transport.json')
pins={H/x['path']:x['sha256'] for x in full['artifacts']+native['artifacts']+native['checkpoints']}
for p,d in pins.items():assert sha(p)==d,p
out=P/'archives';out.mkdir(exist_ok=True);groups=[];group=[];size=0
for p in sorted(paths):
    n=p.stat().st_size;assert n<85000000,p
    if group and size+n>85000000:groups.append(group);group=[];size=0
    group.append(p);size+=n
if group:groups.append(group)
result=[]
for i,ps in enumerate(groups):
    zpath=out/f'replay147-part{i:02d}.zip';assert not zpath.exists()
    members=[]
    with zipfile.ZipFile(zpath,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for p in ps:
            name=p.relative_to(R).as_posix();d=sha(p)
            z.write(p,name)
            members.append(dict(path=name,bytes=p.stat().st_size,sha256=d))
    assert zpath.stat().st_size<100000000
    with zipfile.ZipFile(zpath) as z:
        assert z.namelist()==[x['path'] for x in members]
        for x in members:
            with z.open(x['path']) as f:assert digest(f)==x['sha256'],x['path']
    result.append(dict(path=zpath.relative_to(R).as_posix(),bytes=zpath.stat().st_size,sha256=sha(zpath),members=members))
    print('ARCHIVED',i,len(members),zpath.stat().st_size,flush=True)
receipt=dict(status='PASS_BYTE_VERIFIED_REPLAY_ARCHIVES',archives=result,
    member_count=len(paths),total_original_bytes=sum(p.stat().st_size for p in paths),
    original_files_retained=True,full_sources_prepared_not_all_Lean_checked=True,
    restore_base=str(R),scope='Exact immutable inputs and complete generated sources. Proof acceptance remains recorded separately in module receipts.')
(P/'data/replay-archives.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print(receipt['status'],len(result),len(paths),flush=True)
