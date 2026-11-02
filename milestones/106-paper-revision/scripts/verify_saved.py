"""Freeze or verify the reviewed paper, immutable batch evidence and handovers."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
c=read(HERE/'data/checkpoint.json');manifest=HERE/'data/file-manifest.json'
assert c['status']=='PASS_PAPER106_SOURCE_WITH_COMPILER_UNAVAILABLE'
assert sha((ROOT/c['prior_checkpoint']).read_bytes())==c['prior_checkpoint_sha256']
for name,key in [('verification.json','verification_sha256'),('revision.json','revision_sha256'),('compile-diagnostic.json','compile_diagnostic_sha256'),('batch-observation.json','batch_observation_sha256')]:
    assert sha((HERE/'data'/name).read_bytes())==c[key]
assert sha((HERE/'audit/independent-review.md').read_bytes())==c['independent_review_sha256']
paper=(ROOT/'paper/snake9_research.tex').read_bytes()
assert paper==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert sha(paper)==c['paper_sha256']
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists()
    paths=[p for p in HERE.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts]
    paths += [ROOT/p for p in read(HERE/'data/additional-batch-evidence.json')]
    paths += [ROOT/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/README.md','paper/snake9_research.tex']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(set(paths))]
    manifest.write_text(json.dumps(dict(status='SAVED_PAPER106_AND_CONTINUATION',files=rows,
        scope='Exact revised source, preservation/math checks, compiler failure diagnostic, immutable partial-batch evidence and continuation. No new bound, completed graph certificate or verified PDF.'),indent=2)+'\n',encoding='utf-8')
    print('SAVED_MANIFEST',len(rows),'files')
else:
    rows=read(manifest)['files']
    for r in rows:
        raw=(ROOT/r['path']).read_bytes();assert len(raw)==r['bytes'] and sha(raw)==r['sha256'],r['path']
    if '--staged' in sys.argv:
        names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
        actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=ROOT,text=True).splitlines()
        assert set(actual)==set(names),'Index differs from reviewed manifest'
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+50]],cwd=ROOT,text=True) for i in range(0,len(names),50))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if not name.startswith(('milestones/104-','milestones/106-')):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
