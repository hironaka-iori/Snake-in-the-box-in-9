"""Verify and stage only the immutable running checkpoint and accepted prefix."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    d=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):d.update(b)
    return d.hexdigest()
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'; checkpoint=read(H/'data/checkpoint.json')
assert checkpoint['status']=='PASS_ACCEPTED_PREFIX_FULL_REPLAY_RUNNING'
for p,d in checkpoint['protected_unrelated_files_sha256'].items():assert sha(R/p)==d,p
if not manifest.exists():
    assert len(sys.argv)==1
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()==checkpoint['base_commit']
    archive=read(H/'data/strengthening-archive.json')
    assert sha(H/archive['archive'])==archive['sha256']
    archived={H/x['path'] for x in archive['members']}
    mutable={H/'data/serialization-1793742438473223500.json',H/'data/final-continuation-progress.json'}
    selected=set()
    for folder,dirs,files in os.walk(H):
        dirs[:]=[d for d in dirs if not d.startswith('build') and d!='__pycache__']
        for name in files:
            p=Path(folder)/name
            if p in mutable or p in archived or p==manifest:continue
            if p.suffix in ['.olean','.ilean','.pending','.tmp','.lock'] or name=='stage-paths.nul':continue
            if name.startswith('serialization-final-') or name.startswith('continuation-'):continue
            selected.add(p)
    for row in read(H/'data/accepted-prefix-files.json')['files']:
        p=R/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'];selected.add(p)
    selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
        'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md'])
    assert not any(p in selected for p in mutable)
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
    record=dict(status='EXACT152_RUNNING_CHECKPOINT_MANIFEST',accepted_modules=checkpoint['accepted151_modules'],
        complete_replay=False,files=rows,live_progress_and_controller_files_excluded=True)
    manifest.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
rows=read(manifest)['files']
for row in rows:
    p=R/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
paths=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
if '--stage' in sys.argv:
    assert not subprocess.check_output(g+['diff','--cached','--name-only'],cwd=R,text=True).strip()
    plist=H/'data/stage-paths.nul';plist.write_bytes(b'\0'.join(p.encode() for p in paths)+b'\0')
    subprocess.run(g+['add','-f','--pathspec-from-file='+str(plist),'--pathspec-file-nul'],cwd=R,check=True)
if '--stage' in sys.argv or '--check-staged' in sys.argv:
    staged={p.decode() for p in subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0') if p}
    assert staged==set(paths),(staged-set(paths),set(paths)-staged)
    child=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for path in paths:
        child.stdin.write((':'+path+'\n').encode());child.stdin.flush()
        header=child.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob',header
        left=int(header[2]);d=hashlib.sha256()
        while left:
            data=child.stdout.read(min(left,1048576));assert data;d.update(data);left-=len(data)
        assert child.stdout.read(1)==b'\n' and d.hexdigest()==sha(R/path),path
    child.stdin.close();assert child.wait()==0
print(json.dumps(dict(status='PASS_EXACT152_RUNNING_CHECKPOINT_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),
    accepted_modules=checkpoint['accepted151_modules'],staged_checked='--stage' in sys.argv or '--check-staged' in sys.argv)))
