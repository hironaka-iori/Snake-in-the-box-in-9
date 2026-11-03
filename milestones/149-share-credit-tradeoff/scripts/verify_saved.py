"""Audit and stage the exact fixed-profile obstruction checkpoint."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
Q=R/'milestones/147-countfree-clause-semantics'
P=R/'milestones/148-actual-snake-share-transfer'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        d=hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b)
        cache[key]=d.hexdigest()
    return cache[key]
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
    assert len(sys.argv)==1
    base='84d1d41b840c7b1906012304c301774eb755b5b4'
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()==base
    review=read(H/'audit/graph-review.json')
    assert review['status']=='PASS_INDEPENDENT_SELECTED_ROW_AND_ALL_CREDIT_OBSTRUCTION_AUDIT'
    assert (H/'audit/graph-review.md').is_file()
    for p,d in review['source_files_sha256'].items():assert sha(R/p)==d,p
    for file in ['saved-potential-test.json','new-potential.json']:
        j=read(H/'data'/file)
        for p,d in j['source_files_sha256'].items():assert sha(R/p)==d,p
    test=read(H/'data/saved-potential-test.json');search=read(H/'data/new-potential.json')
    assert test['status']=='SAVED_POTENTIAL_REJECTS_WEAKER_FLOOR'
    assert (test['changed_edges'],test['violated_edges'])==(66567,21861)
    assert search['status']=='PASS_FIXED_CREDIT_ALL_SLOPE_RANGE_OBSTRUCTION'
    assert (search['length'],search['weight'],search['deficit'])==(28,13280,608)
    assert not any(row['event'] for row in search['walk'])
    assert not (H/'data/half-credit.json').exists() and not (H/'scripts/test_half_credit.py').exists()
    assert sha(H/'scripts/check_saved_potential.py')==test['script_sha256']
    assert sha(H/'scripts/find_potential.py')==search['script_sha256']
    receipt=H/'data/CreditTradeoff149-audit.json';lean=read(receipt)
    assert lean['status']=='PASS' and lean['exit_code']==0 and lean['stop_reason'] is None
    for field,digest in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
        assert sha(lean[field])==lean[digest]
    assert sha(H/'scripts/check_module.py')==lean['checker_sha256']
    folder=Path(lean['log']).parent
    assert sha(folder/'source.lean.txt')==lean['source_sha256']
    assert sha(folder/'checker.py.txt')==lean['checker_sha256']
    for p,d in lean['dependencies'].items():assert sha(p)==d,p
    source=Path(lean['source']).read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    assert source.count('#print axioms')==len(lean['axioms'])==5
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in lean['axioms'])
    serials=list((H/'data').glob('serialization-*.json'));assert len(serials)==1
    serial=read(serials[0]);assert serial['status']=='RESUMED'
    assert serial['resume_return_code']==0 and serial['transfer_exit_code']==0 and serial['replay_pid']==15228
    paper=read(H/'data/paper-source-review.json')
    assert paper['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
    assert sha(R/'paper/snake9_research.tex')==paper['source_sha256']
    assert sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==paper['source_sha256']
    assert paper['new_definitions']==0 and not paper['pdf_rebuilt']
    # Verify the previous local transfer receipt without rechecking or rewriting it.
    inherited=read(P/'data/ShareFromCore148-audit.json')
    assert inherited['status']=='PASS'
    assert sha(inherited['source'])==inherited['source_sha256']
    assert sha(inherited['object'])==inherited['olean_sha256']
    progress=(Q/'replay/data/full-replay-progress.json').read_bytes();live=json.loads(progress)
    assert live['status']=='RUNNING' and live['pid']==15228
    assert sha(Q/'scripts/run_full_replay.py')==live['driver_sha256']
    assert sha(Q/'scripts/check_full_replay.py')==live['checker_sha256']
    assert sha(Q/'replay/data/full-execution-plan.json')==live['plan_sha256']
    cmd='Get-CimInstance Win32_Process -Filter "ProcessId=15228" | Select-Object ProcessId,CommandLine,CreationDate | ConvertTo-Json -Compress'
    proc=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
    assert proc['ProcessId']==15228 and 'run_full_replay.py' in proc['CommandLine']
    assert proc['CreationDate']==serial['replay_process']['CreationDate']
    snapshot=H/'data/live-replay-snapshot.json';snapshot.write_bytes(progress)
    protected=read(P/'data/checkpoint.json')['protected_unrelated_files_sha256']
    for p,d in protected.items():assert sha(R/p)==d,p
    verification=dict(status='PASS_FIXED_GRAPH_ALL_CREDIT_OBSTRUCTION',
        source_graph_edges=4947008,source_graph_states=1601856,
        graph_review_sha256=sha(H/'audit/graph-review.json'),graph_review_text_sha256=sha(H/'audit/graph-review.md'),
        lean_receipt_sha256=sha(receipt),lean_arithmetic_statements=5,
        graph_facts_are_explicit_lean_premises=True,new_global_upper_bound=False,
        numerical_experiments=2,half_credit_experiment_run=False,
        live_replay_session=67526,live_replay_process=proc,live_modules_observed=len(live['checked_modules']),
        live_snapshot_sha256=sha(snapshot),paper_sha256=paper['source_sha256'],pdf_rebuilt=False,
        selected_next_task='Continue the same full147 replay; audit its completed contradiction and check the prepared148 final actual-snake composition.',
        removed_28walk_occurrences_in_later144=len(review['removed_in_later144_graph']['new_walk']))
    (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
    checkpoint=dict(status=verification['status'],goal_status='ACTIVE',round_status='PROGRESS',base_commit=base,
        verification_sha256=sha(H/'data/verification.json'),prior_checkpoint_sha256=sha(P/'data/checkpoint.json'),
        current_interval=[191,235],interval_scope='Maintained contributor upper theorem; complete independent rebuild pending.',
        conditional234_premises_unchanged=True,selected_next_task=verification['selected_next_task'],
        active_replay_session=67526,active_replay_pid=15228,live_snapshot_is_observation_only=True,
        unconditional_012301_share16_complete=False,full_paper_revision_last=146,full_paper_revision_next=156,
        paper_sha256=paper['source_sha256'],pdf_rebuilt=False,protected_unrelated_files_sha256=protected)
    (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
    chosen=set()
    for folder,dirs,files in os.walk(H):
        dirs[:]=[d for d in dirs if not d.startswith('build') and d!='__pycache__']
        for name in files:
            p=Path(folder)/name
            if p==manifest or p.suffix in ['.olean','.ilean','.pending','.tmp','.lock'] or name=='stage-paths.nul':continue
            chosen.add(p)
    chosen.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
        'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(chosen)]
    manifest.write_text(json.dumps(dict(status='EXACT_149_PUBLICATION_MANIFEST',files=rows),indent=2)+'\n',encoding='utf-8')
rows=read(manifest)['files']
for x in rows:assert sha(R/x['path'])==x['sha256'] and (R/x['path']).stat().st_size==x['bytes'],x['path']
paths=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
if '--stage' in sys.argv:
    assert not subprocess.check_output(g+['diff','--cached','--name-only'],cwd=R,text=True).strip()
    plist=H/'data/stage-paths.nul';plist.write_bytes(b'\0'.join(p.encode() for p in paths)+b'\0')
    subprocess.run(g+['add','-f','--pathspec-from-file='+str(plist),'--pathspec-file-nul'],cwd=R,check=True)
if '--stage' in sys.argv or '--check-staged' in sys.argv:
    staged={p.decode() for p in subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0') if p}
    assert staged==set(paths),(staged-set(paths),set(paths)-staged)
    proc=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for path in paths:
        proc.stdin.write((':'+path+'\n').encode());proc.stdin.flush()
        header=proc.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob',header
        left=int(header[2]);d=hashlib.sha256()
        while left:
            data=proc.stdout.read(min(left,1048576));assert data;d.update(data);left-=len(data)
        assert proc.stdout.read(1)==b'\n' and d.hexdigest()==sha(R/path),path
    proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_EXACT149_PUBLICATION_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),staged_checked='--stage' in sys.argv or '--check-staged' in sys.argv)))
