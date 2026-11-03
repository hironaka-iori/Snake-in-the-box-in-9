"""Check the saved milestone evidence and, optionally, its exact Git index."""
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=read(H/'data/checkpoint.json');v=read(H/'data/verification.json')
assert c['status']==v['status']=='PASS_ACTUAL_OUTER_RESTRICTION_AND_REFERENCE_REDUCTION'
assert sha(H/'data/verification.json')==c['verification_sha256']
assert sha(R/c['prior_checkpoint'])==c['prior_checkpoint_sha256']
assert sha(R/'paper/snake9_research.tex')==c['paper_sha256']
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
if editor.exists():assert sha(editor)==c['paper_sha256']
assert not (H/'data/check.lock').exists(),'Milestone compiler still active'
for p,d in v['pins'].items():assert sha(H/p)==d,p
review=read(H/'data/final-receipt-review.json')
assert review['status']=='PASS_ACTUAL_OUTER_AND_REFERENCE_RECEIPTS'
assert (review['reviewed_modules'],review['axiom_reports'])==(26,11)
assert review['reference_literal_check']['remaining']==1363
for p,d in review['verified_file_hashes'].items():assert sha(R/p)==d,p
for row in review['modules']:
    q=read(R/row['receipt'])
    assert sha(R/row['receipt'])==row['receipt_sha256']
    assert q['status']=='PASS_REFERENCE_RECOVERY_MODULE' and q['exit_code']==0 and not q['timeout']
    for a in q['theorem_audits']:assert set(a['axioms'])<=set(['propext','Classical.choice','Quot.sound'])
graph=read(H/'data/outer3/results.json')
assert graph['additional_to119']==63
for p,bound in zip(graph['profiles'],[235,234]):
    assert p['all_edge_inequalities_checked'] and p['comparison_integer_bound']==bound
for n,row in c['batch_observations'].items():assert sha(H/row['observation'])==row['sha256']
manifest=H/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists()
    paths=[p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts]
    paths += [R/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(paths))]
    assert all(x['bytes']<100000000 for x in rows)
    manifest.write_text(json.dumps(dict(status='SAVED_CHECKED_OUTER_RESTRICTION120',files=rows,scope='All sources, proofs, exports, checked objects, attempts and audits retained. Local theorem and three reference cases checked; no improved global bound.'),indent=2)+'\n',encoding='utf-8')
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
            if not name.startswith('milestones/120-'):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
