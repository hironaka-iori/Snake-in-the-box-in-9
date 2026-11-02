"""Freeze or verify owned milestone and current-handover files."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest();manifest=HERE/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    r=json.loads((HERE/'data/checkpoint.json').read_text())
    assert r['status']=='PASS_FORTY_SHORT_RULE_RETENTION'
    assert sha((HERE/'data/proof-summary.json').read_bytes())==r['proof_summary_sha256']
    assert sha((HERE/'audit/final-review.md').read_bytes())==r['independent_review_sha256']
    paths=[p for p in HERE.rglob('*') if p.is_file() and p!=manifest
           and not {'build','__pycache__'} & set(p.relative_to(HERE).parts)]
    paths += [ROOT/x for x in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
        'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))
          for p in sorted(set(paths))]
    manifest.write_text(json.dumps(dict(status='SAVED_EXACT_SHORT_RULE_CHECKPOINT',files=rows,
        scope='Milestone sources, receipts and current handover; compiled caches excluded.'),indent=2)+'\n')
    print('SAVED_MANIFEST',len(rows),'files')
else:
    rows=json.loads(manifest.read_text())['files']
    for row in rows:
        raw=(ROOT/row['path']).read_bytes()
        assert len(raw)==row['bytes'] and sha(raw)==row['sha256'],row['path']
    if '--staged' in sys.argv:
        names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[j:j+80]],cwd=ROOT,text=True)
                      for j in range(0,len(names),80))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if name.endswith('.md') and not name.startswith('milestones/81-'):
                raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
