"""Freeze and check exact recovered proof and continuation evidence."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest()
c=read(HERE/'data/checkpoint.json');manifest=HERE/'data/file-manifest.json'
assert c['status']=='PASS_RELAXED_EXCLUSION_AND_EIGHT_ENTRIES'
assert sha((ROOT/c['prior_checkpoint']).read_bytes())==c['prior_checkpoint_sha256']
for path,key in [('data/proof-summary.json','proof_summary_sha256'),('data/batch-observation.json','batch_observation_sha256'),('audit/final-review.md','final_review_sha256'),('mathematical-note.md','mathematical_note_sha256')]:assert sha((HERE/path).read_bytes())==c[key]
assert not (HERE/'data/check.lock').exists()
paper=(ROOT/'paper/snake9_research.tex').read_bytes()
assert paper==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes() and sha(paper)==c['paper_sha256']
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists()
    paths=[p for p in HERE.rglob('*') if p.is_file() and p!=manifest and not {'build','build-isolated','__pycache__'} & set(p.relative_to(HERE).parts)]
    paths += [ROOT/p for p in read(HERE/'data/additional-batch-evidence.json')]
    paths += [ROOT/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(set(paths))]
    manifest.write_text(json.dumps(dict(status='SAVED_RELAXED_REFERENCE_RECOVERY',files=rows,
        scope='Relaxed three-count exclusion, seven covered entries plus prior first entry, remaining1370-entry equivalence, exact inputs/proofs/attempts and immutable graph-batch observation. No new numerical bound or full catalogue.'),indent=2)+'\n',encoding='utf-8')
    print('SAVED_MANIFEST',len(rows),'files',sum(r['bytes'] for r in rows),'bytes')
else:
    rows=read(manifest)['files']
    for r in rows:
        raw=(ROOT/r['path']).read_bytes();assert len(raw)==r['bytes'] and sha(raw)==r['sha256'],r['path']
    if '--staged' in sys.argv:
        names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
        actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=ROOT,text=True).splitlines()
        assert set(actual)==set(names),'Index differs from reviewed manifest'
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+40]],cwd=ROOT,text=True) for i in range(0,len(names),40))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if not name.startswith(('milestones/104-','milestones/108-')):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
