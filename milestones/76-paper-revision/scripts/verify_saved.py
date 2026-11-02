"""Freeze the saved-file manifest or verify its exact staged bytes."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=HERE/'data/file-manifest.json'
if '--staged' not in sys.argv:
    v=json.loads((HERE/'data/verification.json').read_text())
    r=json.loads((HERE/'data/revision.json').read_text())
    c=json.loads((HERE/'data/editor-compile.json').read_text())
    review=json.loads((HERE/'audit/second-review.json').read_text())
    paper=ROOT/'paper/snake9_research.tex'
    assert sha(paper.read_bytes())==v['paper_sha256']==r['paper_sha256']==c['paper_sha256']==review['paper_sha256']
    assert review['status']=='PASS_MATHEMATICAL_AND_SCOPE_REVIEW'
    r['status']='SOURCE_VERIFIED_COMPILATION_BLOCKED'
    r['verification_receipt']='data/verification.json'
    r['arithmetic_receipt']='data/arithmetic-audit.json'
    (HERE/'data/revision.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    paths=[p for p in HERE.rglob('*') if p.is_file() and p!=manifest and not {'build','__pycache__'}&set(p.relative_to(HERE).parts)]
    paths.append(paper)
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(paths)]
    manifest.write_text(json.dumps(dict(status='SAVED_FILE_MANIFEST',files=rows,
      scope='Exact current bytes, excluding generated build objects and this manifest itself. Live case7305 files remain outside this snapshot.'),indent=2)+'\n',encoding='utf-8')
    print('SAVED_MANIFEST',len(rows),'files')
else:
    rows=json.loads(manifest.read_text())['files']
    index=subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--','milestones/76-paper-revision','paper/snake9_research.tex'],cwd=ROOT,text=True)
    blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
    for row in rows:
        raw=(ROOT/row['path']).read_bytes()
        assert len(raw)==row['bytes'] and sha(raw)==row['sha256'],row['path']
        header=b'blob '+str(len(raw)).encode()+b'\0'
        assert hashlib.sha1(header+raw).hexdigest()==blobs[row['path']],row['path']
    raw=manifest.read_bytes();key=manifest.relative_to(ROOT).as_posix()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[key]
    print('PASS_EXACT_STAGED_FILES',len(rows)+1)
