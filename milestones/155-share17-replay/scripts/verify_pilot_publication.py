"""Check and stage the immutable numerical checkpoint, excluding archive originals."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
checkpoint=read(H/'data/pilot-checkpoint.json');manifest=H/'data/pilot-publication-manifest.json'
assert checkpoint['status']=='PASS155_PILOT_FULL_SOURCES_PREPARED'
for p,d in read(R/'milestones/154-share17-broader-semantics/data/checkpoint.json')['protected_unrelated_files_sha256'].items():assert sha(R/p)==d,p
if not manifest.exists():
    assert len(sys.argv)==1
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()==checkpoint['base_commit']
    selected=set()
    roots=[H]
    for root in roots:
        for folder,dirs,files in os.walk(root):
            dirs[:]=[d for d in dirs if not d.startswith('build') and d!='__pycache__' and not (root!=H and d=='logs')]
            for name in files:
                p=Path(folder)/name
                if p==manifest or name=='stage-paths.nul':continue
                if p.suffix in ['.olean','.ilean','.pending','.tmp','.lock']:continue
                if root!=H and name in ['replay-progress.json','replay-progress-v2.json']:continue
                selected.add(p)
    selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
        'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','milestones/155-share17-replay/PILOT_CHECKPOINT.md'])
    assert not (H/'data/replay-batch-v2.lock').exists()
    assert not (H/'data/full-replay-batch.lock').exists()
    assert read(H/'data/replay-progress-v2.json')['status']=='PASS_COMPLETE_REPLAY_PILOT'
    assert all(p.stat().st_size<90_000_000 for p in selected)
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
    manifest.write_text(json.dumps(dict(status='EXACT155_PILOT_AND_FULL_PREPARATION_MANIFEST',files=rows,
        pilot_checked=True,complete_contradiction_pending=True),indent=2)+'\n',encoding='utf-8')
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
    assert staged<=set(paths),staged-set(paths)
    # Unchanged files already in HEAD have no staged diff; all index bytes are checked below.
    child=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for path in paths:
        child.stdin.write((':'+path+'\n').encode());child.stdin.flush()
        header=child.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob',header
        left=int(header[2]);d=hashlib.sha256()
        while left:
            data=child.stdout.read(min(left,1048576));assert data;d.update(data);left-=len(data)
        assert child.stdout.read(1)==b'\n' and d.hexdigest()==sha(R/path),path
    child.stdin.close();assert child.wait()==0
print(json.dumps(dict(status='PASS_EXACT155_PILOT_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),
    staged_checked='--stage' in sys.argv or '--check-staged' in sys.argv)))
