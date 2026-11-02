"""Freeze or verify exact local/staged handover files, excluding build objects."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=HERE/'data/file-manifest.json'
extra=['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
       'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']
if '--staged' not in sys.argv and '--verify' not in sys.argv:
    p=json.loads((HERE/'data/proof-summary.json').read_text())
    assert p['status']=='PASS_NUMERIC_HISTORY_AND_ENCODED_STATE_SEQUENCE'
    paths=[q for q in HERE.rglob('*') if q.is_file() and q!=manifest and
           not {'build','__pycache__'}&set(q.relative_to(HERE).parts)]
    paths += [ROOT/q for q in extra]
    rows=[dict(path=q.relative_to(ROOT).as_posix(),bytes=q.stat().st_size,
               sha256=sha(q.read_bytes())) for q in sorted(paths)]
    manifest.write_text(json.dumps(dict(status='SAVED_EXACT_LOCAL_FILES',files=rows,
        scope='Sources, evidence, diagnostics and handover; existing build objects and live case files are excluded.'),indent=2)+'\n')
    print('SAVED_MANIFEST',len(rows),'files')
else:
    rows=json.loads(manifest.read_text())['files']
    for row in rows:
        raw=(ROOT/row['path']).read_bytes()
        assert len(raw)==row['bytes'] and sha(raw)==row['sha256'],row['path']
    if '--staged' in sys.argv:
        index=subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',
            HERE.relative_to(ROOT).as_posix(),*extra],cwd=ROOT,text=True)
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for row in rows+[dict(path=manifest.relative_to(ROOT).as_posix())]:
            raw=(ROOT/row['path']).read_bytes()
            # Root Markdown follows the repository's LF policy; milestone bytes are exact.
            if row['path'] in extra:raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[row['path']],row['path']
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
