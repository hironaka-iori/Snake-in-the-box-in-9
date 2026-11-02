"""Freeze or verify exact paper, milestone and current handover bytes."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest();manifest=HERE/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    r=json.loads((HERE/'data/checkpoint.json').read_text())
    assert r['status']=='PAPER86_SOURCE_VERIFIED_COMPILER_UNAVAILABLE'
    assert sha((ROOT/'paper/snake9_research.tex').read_bytes())==r['paper_sha256']
    for path,key in [('data/verification.json','verification_sha256'),('data/logic-audit.json','logic_audit_sha256'),
                     ('data/bonus-audit.json','bonus_audit_sha256'),
                     ('data/editor-compile-final.json','editor_compile_sha256'),('audit/post-edit-review.md','post_edit_review_sha256')]:
        assert sha((HERE/path).read_bytes())==r[key]
    paths=[p for p in HERE.rglob('*') if p.is_file() and p!=manifest
           and not {'build','__pycache__'} & set(p.relative_to(HERE).parts)]
    paths += [ROOT/x for x in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
        'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))
          for p in sorted(set(paths))]
    manifest.write_text(json.dumps(dict(status='SAVED_PAPER86',files=rows,
        scope='Exact paper and mirror hash, sources, receipts, successful replay-log snapshot and current handover. Build caches excluded.'),indent=2)+'\n')
    print('SAVED_MANIFEST',len(rows),'files')
else:
    rows=json.loads(manifest.read_text())['files']
    for row in rows:
        raw=(ROOT/row['path']).read_bytes()
        assert len(raw)==row['bytes'] and sha(raw)==row['sha256'],row['path']
    assert (ROOT/'paper/snake9_research.tex').read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
    if '--staged' in sys.argv:
        names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[j:j+60]],cwd=ROOT,text=True)
                      for j in range(0,len(names),60))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if not name.startswith('milestones/86-') and (name.endswith('.md') or name=='paper/snake9_research.tex'):
                raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
