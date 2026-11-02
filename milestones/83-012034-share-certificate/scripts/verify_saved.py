"""Freeze or verify this partial case and its exact current handover."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
sha=lambda b:hashlib.sha256(b).hexdigest();manifest=HERE/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    checkpoint=json.loads((HERE/'data/checkpoint.json').read_text())
    assert checkpoint['status']=='PARTIAL_SHARE20_SEMANTICS_AND_EXACT_CONDITIONAL_COMPARISON'
    for path,digest in checkpoint['evidence_sha256'].items():assert sha((ROOT/path).read_bytes())==digest
    paths=[p for p in HERE.rglob('*') if p.is_file() and p!=manifest
           and not {'build','__pycache__'} & set(p.relative_to(HERE).parts)]
    paths += [ROOT/x for x in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
        'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md',
        'milestones/73-countfree-share-catalogue/NEXT.md']]
    paths += [CASE/'README.md']+list((CASE/'scripts').glob('*.py'))+list((CASE/'data').glob('*.json'))
    pending=json.loads((CASE/'data/pending-checkpoint.json').read_text())
    paths += [CASE/p['path'] for r in pending['archives'] for p in r.get('parts',[r])]
    paths += [CASE/'logs'/x for x in ['semantic-record.json','composition-record.json','lrat-generate.log','lrat-slice-export.log']]
    paths += [CASE/r['log'] for r in pending['compiled_modules']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))
          for p in sorted(set(paths))]
    assert all(row['bytes']<100*1024*1024 for row in rows)
    manifest.write_text(json.dumps(dict(status='SAVED_PARTIAL_SHARE20_AND_CONDITIONAL_COMPARISON',files=rows,
        scope='Exact source/proof archives, fixed semantic receipts, current task and handover. Live completion log and build caches excluded; progress observation frozen separately.'),indent=2)+'\n')
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
            if name.endswith('.md') and not name.startswith(('milestones/83-','milestones/73-')):
                raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
