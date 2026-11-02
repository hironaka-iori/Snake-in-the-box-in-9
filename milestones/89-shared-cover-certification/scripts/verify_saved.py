"""Freeze and verify exact owned evidence plus current shared summaries."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest();manifest=HERE/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    r=json.loads((HERE/'data/checkpoint.json').read_text())
    assert r['status']=='PASS_SHARED_COVER_INFRASTRUCTURE_PARTIAL_FINITE_BATCH'
    assert sha((HERE/'data/proof-summary.json').read_bytes())==r['proof_summary_sha256']
    assert sha((ROOT/'paper/snake9_research.tex').read_bytes())==r['paper_sha256']
    proof=json.loads((HERE/'data/proof-summary.json').read_text())
    completed={row['module'] for row in proof['modules']}
    def stable_file(p):
        import re
        rel=p.relative_to(HERE)
        if not p.is_file() or p==manifest or {'build','__pycache__'} & set(rel.parts):return False
        if rel.as_posix() in ['data/balanced-cover-active.json','logs/case7302-unique-resume-run.json']:return False
        if rel.parts[0]=='logs' and p.name.startswith('balanced-cover-run-'):return False
        if rel.parts[0] in ['logs','data']:
            module=p.name.split('-',1)[0].split('.',1)[0]
            if re.fullmatch(r'(?:Balanced(?:Graph|[0-9]{3})|Cover[0-9]{3})(?:Data|Checks)',module):
                if module not in completed and module!='Cover001Checks':return False
        return True
    paths=[p for p in HERE.rglob('*') if stable_file(p)]
    paths += [ROOT/x for x in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
        'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(set(paths))]
    manifest.write_text(json.dumps(dict(status='SAVED_SHARED_COVER89',files=rows,
        scope='Exact generated sources, completed proofs at this checkpoint, context witnesses, stopped experiments, frozen run observations and current handover. Active run records and output logs excluded. Build objects excluded; inherited proof status remains explicit.'),indent=2)+'\n')
    print('SAVED_MANIFEST',len(rows),'files')
else:
    rows=json.loads(manifest.read_text())['files']
    for row in rows:
        raw=(ROOT/row['path']).read_bytes();assert len(raw)==row['bytes'] and sha(raw)==row['sha256'],row['path']
    paper=(ROOT/'paper/snake9_research.tex').read_bytes()
    assert paper==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
    assert sha(paper)==json.loads((HERE/'data/checkpoint.json').read_text())['paper_sha256']
    if '--staged' in sys.argv:
        names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[j:j+60]],cwd=ROOT,text=True)
            for j in range(0,len(names),60))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if not name.startswith('milestones/89-'):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
