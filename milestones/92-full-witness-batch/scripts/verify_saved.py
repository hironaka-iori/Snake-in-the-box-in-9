"""Freeze immutable evidence while excluding mutable and unfinished proof jobs."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=HERE/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    c=json.loads((HERE/'data/checkpoint.json').read_text())
    assert c['status'] in ['PASS_CONTEXT_ASSIGNMENT_PARTIAL_WITNESS_BATCH','PASS_ALL_CLASSES_AND_NUMERIC_DIAGRAM']
    assert sha((HERE/'data/proof-summary.json').read_bytes())==c['proof_summary_sha256']
    s=json.loads((HERE/'data/proof-summary.json').read_text())
    modules={r['module'] for r in s['modules']}
    paths=[]
    for p in HERE.rglob('*'):
        if not p.is_file() or p==manifest:continue
        parts=p.relative_to(HERE).parts
        if {'build','__pycache__'} & set(parts):continue
        if p.name in ['witness-batch.lock','witness-batch-active.json']:continue
        if p.suffix=='.tmp':continue
        if parts[0]=='logs':
            if p.name.startswith('witness-batch-run-'):continue
            stem=p.name.removesuffix('-record.json').removesuffix('-resource-snapshot.json').removesuffix('.log')
            if stem not in modules and not p.name.startswith('ContextAssignmentChecks-timeout-'):continue
        if parts[0]=='data' and p.name.endswith('-audit.json'):
            if p.name.removesuffix('-audit.json') not in modules:continue
        paths.append(p)
    g=json.loads((HERE/'data/geometry-observation.json').read_text())
    paths += [ROOT/name for name in g['archive_paths']]
    paths += [ROOT/name for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
                                   'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(set(paths))]
    manifest.write_text(json.dumps(dict(status='SAVED_BATCH92',files=rows,
        scope='Generated all-class sources, checked context assignment, completed witness receipts at snapshot, frozen live-job records, new geometry receipts and handover. Unfinished logs, mutable records and build objects excluded; no complete dependency rebuild.'),indent=2)+'\n')
    print('SAVED_MANIFEST',len(rows),'files',sum(r['bytes'] for r in rows),'bytes')
else:
    rows=json.loads(manifest.read_text())['files']
    for r in rows:
        raw=(ROOT/r['path']).read_bytes()
        assert len(raw)==r['bytes'] and sha(raw)==r['sha256'],r['path']
    paper=(ROOT/'paper/snake9_research.tex').read_bytes()
    assert paper==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
    assert sha(paper)==json.loads((HERE/'data/checkpoint.json').read_text())['paper_sha256']
    if '--staged' in sys.argv:
        names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+60]],cwd=ROOT,text=True)
                      for i in range(0,len(names),60))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if not name.startswith(('milestones/89-','milestones/90-','milestones/91-','milestones/92-')):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
