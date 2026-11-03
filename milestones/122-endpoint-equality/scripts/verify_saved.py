"""Save or verify the immutable research snapshot; live batch files stay separate."""
from pathlib import Path
import datetime,hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
review=read(H/'data/proof-review.json')
assert review['status']=='PASS_67_ENDPOINT_MODULE_RECEIPTS'
assert (review['reviewed_modules'],review['axiom_reports'])==(67,24)
for p,d in {**review['verified_file_hashes'],**review['additional_pins']}.items():assert sha(R/p)==d,p
assert sha(H/'scripts/audit_receipts.py')==review['script_sha256']
names={m['module'] for m in review['modules']}
for m in review['modules']:
    p=R/m['receipt'];a=read(p);assert sha(p)==m['receipt_sha256']
    assert a['status']=='PASS_REFERENCE_RECOVERY_MODULE' and a['exit_code']==0 and not a['timeout']
    assert all(set(x['axioms'])<=set(['propext','Classical.choice','Quot.sound']) for x in a['theorem_audits'])
pending=read(H/'data/pending-plan.json');assert len(pending['modules'])==381
for p,d in pending['pins'].items():assert sha(H/p)==d,p
graph=read(H/'data/endpoint-graph/summary.json')
assert graph['eligible_retained_keys']==9577
assert graph['completed_credit_cases'][0]['C']==4
assert graph['skipped_credit_cases']==[8,16,32,64]
for entry in graph['completed_credit_cases']+[graph['odd_deletion']]:
    assert sha(H/entry['results'])==entry['results_sha256']
    g=read(H/entry['results'])
    for p,d in g['source_files_sha256'].items():assert sha(R/p)==d,p
    assert all(p['all_edge_inequalities_checked'] for p in g['profiles'])
    assert all(p['cycle_eligible']==0 for p in g['profiles'])
    assert [p['mean'] for p in g['profiles']]==['2915/6','496']
obs=read(H/'data/batch-observation.json')
for b in obs['batches']:
    assert sha(H/b['snapshot'])==b['sha256']
    assert b['pid']==b['process']['ProcessId'] and b['batch'] in b['process']['CommandLine']
    if 'checker_snapshot' in b:assert sha(H/b['checker_snapshot'])==b['checker_snapshot_sha256']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='5e62b785321b8b624338e484560f3ac16d048699c841deeccc69573fd13be72f'
manifest=H/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists()
    pins={p.relative_to(H).as_posix():sha(p) for p in [H/'MATHEMATICAL_NOTE.md',H/'data/proof-review.json',
        H/'audit/proof-review.md',H/'data/certificate-input-audit.json',H/'data/pending-plan.json',
        H/'data/batch-observation.json',H/'data/stopped-batches.json',H/'data/endpoint-graph/summary.json',
        H/'data/endpoint-graph/saved-cycle-audit.json',H/'audit/endpoint-graph-review.md',H/'data/next-six-four-cases.json']}
    v=dict(status='PASS_ENDPOINT26_AND_CONDITIONAL_THIRTEEN_COUNT_WITH_GRAPH_LIMIT',pins=pins,
        reviewed_modules=67,axiom_reports=24,universal_endpoint_equality_proved=False,
        pending_modules=381,new_global_upper_bound=False,previous_goal_turn='PROGRESS',
        scope='One closed endpoint case, conditional general equality assembly and occurrence13, exact finite graph obstruction; two endpoint cases and global assembly pending.')
    (H/'data/verification.json').write_text(json.dumps(v,indent=2)+'\n')
    prior=R/'milestones/121-replacement-window-pressure/data/checkpoint.json'
    c=dict(status=v['status'],verification_sha256=sha(H/'data/verification.json'),
        prior_checkpoint=prior.relative_to(R).as_posix(),prior_checkpoint_sha256=sha(prior),
        paper_revision=116,next_paper_revision=126,paper_sha256=sha(paper),
        base_commit='900861facfac2d2dd6a8f9c10aeddbbe3f4fc888',goal_status='ACTIVE',
        batches=obs['batches'],current_interval=[191,235],interval_scope='Maintained prior result with documented independent rebuild limitation; conditional234 remains unresolved.')
    (H/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
    started=read(H/'audit/observed-122-endpoint-equality.json')['started_at']
    cutoff=int(datetime.datetime.fromisoformat(started).timestamp()*1e9)
    selected=[]
    for p in H.rglob('*'):
        if not p.is_file() or p==manifest or '__pycache__' in p.parts:continue
        rel=p.relative_to(H)
        if p.suffix=='.lock' or rel.as_posix()=='data/pending-progress.json':continue
        if rel.parts[0]=='logs' and (p.stat().st_mtime_ns>=cutoff or p.name.startswith(('live-','pending-'))):continue
        if rel.parts[0]=='build-isolated':
            if rel.suffix!='.olean' or '.'.join(rel.with_suffix('').parts[1:]) not in names:continue
        if rel.parts[0]=='data' and p.name.endswith('-audit.json'):
            j=read(p)
            if 'module' in j and j['module'] not in names:continue
        selected.append(p)
    selected += [R/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
        'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(selected))]
    assert all(x['bytes']<100000000 for x in rows)
    manifest.write_text(json.dumps(dict(status='SAVED_IMMUTABLE_ENDPOINT_RESEARCH122',files=rows,
        live_output_cutoff=started,scope='Completed67-module receipts and all three fixed certificate exports included. Live381-module batch outputs are retained locally outside this frozen manifest.'),indent=2)+'\n')
    print('SAVED_MANIFEST',len(rows),sum(x['bytes'] for x in rows),'bytes')
else:
    v=read(H/'data/verification.json');c=read(H/'data/checkpoint.json')
    assert c['status']==v['status']=='PASS_ENDPOINT26_AND_CONDITIONAL_THIRTEEN_COUNT_WITH_GRAPH_LIMIT'
    assert sha(H/'data/verification.json')==c['verification_sha256']
    assert sha(R/c['prior_checkpoint'])==c['prior_checkpoint_sha256']
    for p,d in v['pins'].items():assert sha(H/p)==d,p
    rows=read(manifest)['files']
    for r in rows:
        p=R/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],r['path']
    if '--staged' in sys.argv:
        files=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
        actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=R,text=True).splitlines()
        assert set(actual)==set(files),'Index differs from reviewed snapshot'
        output=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*files[i:i+50]],cwd=R,text=True) for i in range(0,len(files),50))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in output.splitlines()}
        for name in files:
            raw=(R/name).read_bytes()
            if not name.startswith('milestones/122-'):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
