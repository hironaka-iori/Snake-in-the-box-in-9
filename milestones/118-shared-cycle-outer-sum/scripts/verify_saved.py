"""Verify exact saved research evidence and, optionally, the reviewed Git index."""
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=read(H/'data/checkpoint.json');v=read(H/'data/verification.json')
assert c['status']==v['status']=='PASS_LOCAL_COUNTEREXAMPLES_AND_CONDITIONAL_CYCLE_LIMITS'
assert sha(H/'data/verification.json')==c['verification_sha256']
assert sha(R/c['prior_checkpoint'])==c['prior_checkpoint_sha256']
assert sha(R/'paper/snake9_research.tex')==c['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
for p,d in v['pins'].items():assert sha(H/p)==d,p
q=read(H/'data/Witness118-audit.json')
for p,k in [(H/'lean/Witness118.lean','source_sha256'),(H/'scripts/check_witnesses.py','checker_sha256'),(H/'build-geometry/Witness118.olean','olean_sha256'),(H/q['log'],'log_sha256'),(H/q['source_snapshot'],'source_sha256'),(H/q['checker_snapshot'],'checker_sha256')]:assert sha(p)==q[k],str(p)
assert q['status']=='PASS_CONCRETE_LOCAL_FOREST_DATA' and q['exit_code']==0 and not q['timeout']
assert len(q['theorem_audits'])==9
for p,d in q['dependencies'].items():assert sha(Path(p))==d,p
for num,row in c['batch_observations'].items():assert sha(H/row['observation'])==row['sha256']
manifest=H/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists()
    paths=[p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts]
    paths += [R/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(paths))]
    assert all(x['bytes']<100000000 for x in rows)
    manifest.write_text(json.dumps(dict(status='SAVED_LOCAL_LIMITS118',files=rows,scope='Exact local counterexamples, Lean object/source/logs, preserved failed attempt, conditional cycle limits and handover. No new numerical bound.'),indent=2)+'\n',encoding='utf-8')
    print('SAVED_MANIFEST',len(rows),sum(x['bytes'] for x in rows),'bytes')
else:
    rows=read(manifest)['files']
    for row in rows:
        p=R/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
    if '--staged' in sys.argv:
        names=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
        actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=R,text=True).splitlines()
        assert set(actual)==set(names),'Index differs from reviewed manifest'
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+50]],cwd=R,text=True) for i in range(0,len(names),50))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(R/name).read_bytes()
            if not name.startswith('milestones/118-'):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
