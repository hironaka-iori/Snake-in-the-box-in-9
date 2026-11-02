"""Merge pinned first-resolved objects so nested Lean namespaces stay complete."""
from pathlib import Path
import hashlib,json,shutil
from concurrent.futures import ThreadPoolExecutor
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ep=HERE/'data/environment.json';env=json.loads(ep.read_text())
assert not (HERE/'data/check.lock').exists()
original=HERE/'data/environment-before-overlay.json'
if not original.exists():original.write_bytes(ep.read_bytes())
else:env=json.loads(original.read_text())
overlay=HERE/'build/support';overlay.mkdir(exist_ok=True)
seen={};rows=[];duplicates=0
namespace_roots={'LocalWindowCnf','LocalWindowSat','LocalWindowUnsat','Share12','Share120','Share7300','Share7304','Share7305','Share7306'}
for directory in env['paths'][1:]:
    base=Path(directory)
    for p in sorted(base.rglob('*.olean')):
        relative=p.relative_to(base)
        if relative.parts[0] not in namespace_roots:continue
        if relative in seen:duplicates+=1;continue
        seen[relative]=p
def transfer(item):
    relative,p=item;target=overlay/relative
    assert '..' not in relative.parts and target.absolute().is_relative_to(overlay.absolute())
    target.parent.mkdir(parents=True,exist_ok=True)
    digest=sha(p)
    if not target.exists() or target.stat().st_size!=p.stat().st_size or sha(target)!=digest:
        shutil.copyfile(p,target)
    assert sha(target)==digest
    return dict(module=relative.as_posix(),original=p.relative_to(ROOT).as_posix(),sha256=digest,bytes=p.stat().st_size)
with ThreadPoolExecutor(max_workers=8) as pool:
    for row in pool.map(transfer,seen.items()):
        rows.append(row)
        if len(rows)%500==0:print('PINNED_OBJECTS',len(rows),flush=True)
env['paths']=[str(HERE/'build'),str(overlay),*env['paths'][1:]]
env['overlay']=dict(method='copies of exact first-resolved objects in the nine shared nested namespaces; imports only',objects=rows,duplicate_paths_skipped=duplicates,initial_environment_sha256=sha(original))
ep.write_text(json.dumps(env,indent=2)+'\n')
print('COMPLETE_NAMESPACE_OVERLAY',len(rows),'objects;',sum(r['bytes'] for r in rows),'bytes')
