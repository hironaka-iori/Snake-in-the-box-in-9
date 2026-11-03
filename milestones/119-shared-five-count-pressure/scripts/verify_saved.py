"""Verify exact saved research evidence and, optionally, the reviewed Git index."""
from pathlib import Path
import gzip,hashlib,json,os,shutil,subprocess,sys,tempfile
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
archives=read(H/'data/large-artifact-archives.json')
for row in archives['files']:
    packed=H/row['archive'];assert sha(packed)==row['archive_sha256']
    if '--restore-archives' in sys.argv:
        target=(H/row['original']).resolve();assert target.is_relative_to((H/'work').resolve())
        if target.exists():assert target.stat().st_size==row['bytes'] and sha(target)==row['sha256']
        else:
            target.parent.mkdir(parents=True,exist_ok=True)
            fd,name=tempfile.mkstemp(prefix='restore-',dir=target.parent);os.close(fd);temp=Path(name)
            with gzip.open(packed,'rb') as src,temp.open('wb') as dst:shutil.copyfileobj(src,dst,1024*1024)
            assert temp.stat().st_size==row['bytes'] and sha(temp)==row['sha256']
            assert not target.exists();temp.rename(target)
if '--restore-archives' in sys.argv:
    print('PASS_RESTORED_EXACT_NATIVE_PROOFS',len(archives['files']));sys.exit(0)
c=read(H/'data/checkpoint.json');v=read(H/'data/verification.json')
assert c['status']==v['status']=='PASS_ACTUAL_COUNTEREXAMPLE_AND_NATIVE_FULL_CUBE_RESTRICTIONS'
assert sha(H/'data/verification.json')==c['verification_sha256']
assert sha(R/c['prior_checkpoint'])==c['prior_checkpoint_sha256']
assert sha(R/'paper/snake9_research.tex')==c['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
for p,d in v['pins'].items():assert sha(H/p)==d,p
q=read(H/'data/Counterexample119-audit.json')
for p,k in [(H/'lean/Counterexample119.lean','source_sha256'),(H/'scripts/check_counterexample.py','checker_sha256'),(H/'build-geometry/Counterexample119.olean','olean_sha256'),(H/q['log'],'log_sha256'),(H/q['source_snapshot'],'source_sha256'),(H/q['checker_snapshot'],'checker_sha256')]:assert sha(p)==q[k],str(p)
assert q['status']=='PASS_ACTUAL_SNAKE_COUNTEREXAMPLE_AND_COMPARISON' and q['exit_code']==0 and not q['timeout']
assert len(q['theorem_audits'])==9
for p,d in q['dependencies'].items():assert sha(Path(p))==d,p
for num,row in c['batch_observations'].items():assert sha(H/row['observation'])==row['sha256']
manifest=H/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists()
    excluded={x['original'] for x in archives['files']}
    paths=[p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts and p.relative_to(H).as_posix() not in excluded]
    paths += [R/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(paths))]
    assert all(x['bytes']<100000000 for x in rows)
    manifest.write_text(json.dumps(dict(status='SAVED_FULL_CUBE_RESTRICTIONS119',files=rows,large_originals=archives['files'],scope='Exact actual counterexample, native contradiction archives, oriented graph evidence and continuation. Negative Lean work pending; no new numerical bound.'),indent=2)+'\n',encoding='utf-8')
    print('SAVED_MANIFEST',len(rows),sum(x['bytes'] for x in rows),'bytes')
else:
    rows=read(manifest)['files']
    for row in rows:
        p=R/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
    if '--staged' in sys.argv:
        names=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
        actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=R,text=True).splitlines()
        assert set(actual)==set(names),'Index differs from reviewed manifest'
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+50]],cwd=R,text=True) for i in range(0,len(names),50))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(R/name).read_bytes()
            if not name.startswith('milestones/119-'):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
