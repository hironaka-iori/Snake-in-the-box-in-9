"""Pin the inherited count proof closure and copy three roots for fresh checks."""
from pathlib import Path
import hashlib,json,shutil
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
folders=[next((ROOT/'milestones').glob(str(n)+'-*')) for n in [66,65,64,62,61,60,59,58,54,52,51,50,49,48,47,45,44,42,41,31,32,28]]
base=read(ROOT/'milestones/79-retained-edge-guards/data/IntervalGuards-audit.json')['paths']
base.append('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/mathlib/.lake/build/lib/lean')
overlay=HERE/'build/count-support';overlay.mkdir(exist_ok=True)
cache={};modules={};external={};audits={}
roots=['TerminalCount','CountPhase04','CountPhase29'];todo=roots[:]
while todo:
    name=todo.pop()
    if name in modules or name in external:continue
    candidates=[f for f in folders if (f/'lean'/(name+'.lean')).exists() and (f/'logs/build-record.json').exists()]
    found=None
    for folder in candidates:
        if folder not in cache:cache[folder]=read(folder/'logs/build-record.json')
        rec=cache[folder];source=folder/'lean'/(name+'.lean');obj=Path(rec['build'])/(name+'.olean')
        digest=sha(source)
        matching=[r for r in rec['records'] if r['module']==name and r['exit_code']==0 and r['source_sha256']==digest]
        if matching and obj.exists():found=(folder,source,obj,digest);break
    if found is None:
        obj=next((Path(p)/(name+'.olean') for p in base if (Path(p)/(name+'.olean')).exists()),None)
        assert obj is not None,('Missing inherited module',name,candidates)
        external[name]=dict(object=str(obj),object_sha256=sha(obj),scope='Inherited milestone79 environment; not rebuilt here.')
        continue
    folder,source,obj,digest=found
    dest=overlay/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    if not dest.exists() or sha(dest)!=sha(obj):shutil.copyfile(obj,dest)
    modules[name]=dict(source=str(source),source_sha256=digest,object=str(dest),object_sha256=sha(dest),origin=str(obj))
    audits[(folder/'logs/build-record.json').relative_to(ROOT).as_posix()]=sha(folder/'logs/build-record.json')
    if name in roots:
        audit=folder/'data/lean-audit.json';ar=read(audit);assert ar['status']=='PASS'
        assert any(r['module']==name and r['source_sha256']==digest for r in ar['records'])
        audits[audit.relative_to(ROOT).as_posix()]=sha(audit)
        shutil.copyfile(source,HERE/'lean'/(name+'.lean'))
    for line in source.read_text(encoding='utf-8-sig').splitlines():
        if line.startswith('import '):todo.extend(t.replace('.','/') for t in line.split()[1:])
position=ROOT/'milestones/81-recovered-short-rule-retention'
receipt=position/'data/PositionTransfer-audit.json';ar=read(receipt);assert ar['status']=='PASS_LEAN_MODULE'
for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
    assert sha(position/folder/('PositionTransfer'+ext))==ar[key]
modules['PositionTransfer']=dict(source=str(position/'lean/PositionTransfer.lean'),source_sha256=ar['source_sha256'],
    object=str(position/'build/PositionTransfer.olean'),object_sha256=ar['olean_sha256'],origin=str(receipt))
audits[receipt.relative_to(ROOT).as_posix()]=sha(receipt)
out=dict(status='PINNED_HISTORY_COUNT_SUPPORT',roots=roots,overlay=str(overlay),modules=modules,
    external_imports=external,extra_paths=[str(position/'build')],prior_audit_sha256=audits,
    scope='Three root sources copied exactly for fresh checking. Transitive inherited objects are source-matched and hash-pinned, with the milestone79 environment reused; no clean full closure rebuild.')
(HERE/'data/count-support.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(modules),'pinned modules;',len(external),'inherited imports; 3 copied roots')
