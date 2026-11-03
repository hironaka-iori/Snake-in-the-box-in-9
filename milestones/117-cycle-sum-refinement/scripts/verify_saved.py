"""Freeze/check reviewed files and safely restore the archived native proofs."""
from pathlib import Path
import gzip,hashlib,json,os,shutil,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
archives=read(HERE/'data/large-artifact-archives.json')
for row in archives['files']:
    packed=HERE/row['archive'];assert digest(packed)==row['archive_sha256']
    if '--restore-archives' in sys.argv:
        target=(HERE/row['original']).resolve();assert target.is_relative_to((HERE/'work').resolve())
        if target.exists():assert target.stat().st_size==row['bytes'] and digest(target)==row['sha256']
        else:
            target.parent.mkdir(parents=True,exist_ok=True)
            fd,tempname=tempfile.mkstemp(prefix='restore-',dir=target.parent);os.close(fd)
            temporary=Path(tempname)
            with gzip.open(packed,'rb') as source,temporary.open('wb') as dest:shutil.copyfileobj(source,dest,1024*1024)
            assert temporary.stat().st_size==row['bytes'] and digest(temporary)==row['sha256']
            assert not target.exists();temporary.rename(target)
if '--restore-archives' in sys.argv:
    print('PASS_RESTORED_EXACT_NATIVE_PROOFS',len(archives['files']));sys.exit(0)
c=read(HERE/'data/checkpoint.json');assert c['status']=='PASS_NATIVE_COUNT_REFINEMENT_WITH_CONDITIONAL_LEAN_TRANSFER'
assert digest(ROOT/c['prior_checkpoint'])==c['prior_checkpoint_sha256']
for name,key in [('verification.json','verification_sha256'),('proof-summary.json','proof_summary_sha256'),('graph-audit.json','graph_audit_sha256'),('large-artifact-archives.json','archive_manifest_sha256')]:assert digest(HERE/'data'/name)==c[key]
assert digest(HERE/'audit/final-review.md')==c['final_review_sha256']
assert digest(HERE/'audit/graph-review.md')==c['graph_review_sha256']
assert digest(ROOT/'paper/snake9_research.tex')==c['paper_sha256']==digest(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
manifest=HERE/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists()
    excluded={row['original'] for row in archives['files']}
    paths=[p for p in HERE.rglob('*') if p.is_file() and p!=manifest and not {'build-geometry','__pycache__'}&set(p.parts) and p.relative_to(HERE).as_posix() not in excluded]
    paths += [ROOT/name for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=digest(p)) for p in sorted(set(paths))]
    assert all(row['bytes']<100000000 for row in rows)
    manifest.write_text(json.dumps(dict(status='SAVED_COUNT_SUM_REFINEMENT117',files=rows,large_originals=archives['files'],
        scope='Exact research sources, native proof archives, conditional Lean evidence, bounded probes, graph evidence and continuation. No new global bound.'),indent=2)+'\n',encoding='utf-8')
    print('SAVED_MANIFEST',len(rows),'files',sum(row['bytes'] for row in rows),'bytes')
else:
    rows=read(manifest)['files']
    for row in rows:
        p=ROOT/row['path'];assert p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],row['path']
    if '--staged' in sys.argv:
        names=[row['path'] for row in rows]+[manifest.relative_to(ROOT).as_posix()]
        actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=ROOT,text=True).splitlines()
        assert set(actual)==set(names),'Index differs from reviewed manifest.'
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+50]],cwd=ROOT,text=True) for i in range(0,len(names),50))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if not name.startswith('milestones/117-'):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
