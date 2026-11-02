"""Save and verify exact milestone102 evidence, including staged Git bytes."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=HERE/'data/file-manifest.json'
c=json.loads((HERE/'data/checkpoint.json').read_text())
assert c['status']=='PASS_POTENTIAL_BLOCK_REDUCTION_AND_EIGHT_NEW_CONTEXTS'
assert sha((HERE/'data/proof-summary.json').read_bytes())==c['proof_summary_sha256']
assert sha((ROOT/c['prior_checkpoint']).read_bytes())==c['prior_checkpoint_sha256']
paper=(ROOT/'paper/snake9_research.tex').read_bytes()
assert paper==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert sha(paper)==c['paper_sha256']
assert not (HERE/'data/check.lock').exists()
assert not (HERE/'data/check-extra.lock').exists()
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists(), 'A frozen manifest must not be overwritten.'
    paths=[p for p in HERE.rglob('*') if not {'build','__pycache__'} & set(p.relative_to(HERE).parts)
           and p.is_file() and p!=manifest and p.name!='check.lock']
    paths += [ROOT/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md',
              'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,
               sha256=sha(p.read_bytes())) for p in sorted(set(paths))]
    manifest.write_text(json.dumps(dict(status='SAVED_MILESTONE102',files=rows,
        scope='Checked bounded potential reduction, 412 block equations and six complete contexts per profile, with a matched Boolean comparison. Complete graph certificates remain pending.'),indent=2)+'\n')
    print('SAVED_MANIFEST',len(rows),'files',sum(r['bytes'] for r in rows),'bytes')
else:
    rows=json.loads(manifest.read_text())['files']
    for r in rows:
        raw=(ROOT/r['path']).read_bytes()
        assert len(raw)==r['bytes'] and sha(raw)==r['sha256'],r['path']
    if '--staged' in sys.argv:
        names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
        actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=ROOT,text=True).splitlines()
        assert set(actual)==set(names), 'Staged paths differ from the reviewed manifest.'
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+60]],cwd=ROOT,text=True) for i in range(0,len(names),60))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if not name.startswith('milestones/102-'):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
