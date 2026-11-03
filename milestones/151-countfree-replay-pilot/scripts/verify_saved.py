"""Audit and stage the immutable bounded012032 replay checkpoint."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/150-actual-pair-share';Q=R/'milestones/147-countfree-clause-semantics'
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
    base='245b31cf2549f02e84c192f558c5ae243dd903e2'
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()==base
    pilot=read(H/'data/pilot-completion.json');group=read(H/'data/first-group-completion.json')
    assert pilot['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT'
    assert (pilot['checked_modules'],pilot['axiom_reports'])==(38,120)
    assert group['status']=='PASS_FIRST32_REPLAY_SEGMENTS_AND_CHECKPOINT'
    assert (group['checked_modules'],group['deductions_checked'],group['references_checked'])==(49,3728,195386)
    for p,d in pilot['source_files_sha256'].items():assert sha(R/p)==d,p
    assert sha(H/'data/first-group-progress-snapshot.json')==group['progress_snapshot_sha256']
    assert sha(H/'data/full-execution-plan.json')==group['full_execution_plan_sha256']
    reports=0
    for row in group['receipts']:
        p=H/row['receipt'];assert sha(p)==row['sha256'];j=read(p)
        assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
        for name,digest in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(j[name])==j[digest]
        for p,d in j['dependencies'].items():assert sha(p)==d,p
        folder=Path(j['log']).parent
        assert sha(folder/'source.lean.txt')==j['source_sha256'] and sha(folder/'checker.py.txt')==j['checker_sha256']
        assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in j['axioms'])
        reports+=len(j['axioms'])
    assert reports==153
    review=H/'audit/replay-review.json'
    assert sha(review)=='ed6039bfdfca718e46384b58cff5eee6542010c3dbfee53311bef30c54aab601'
    assert sha(H/'audit/replay-review.md')=='b88853e39f108b415b96ecd7b7f03c0e8e0e0617a1c0f3db4c2aef729b2d484d'
    for p,d in read(review)['pins'].items():assert sha(R/p)==d,p
    for filename in ['preparation.json','full-generator-plan.json','full-replay-runner-plan.json']:
        j=read(H/'data'/filename)
        for field in ['source_files_sha256','generated_sha256','files_sha256']:
            for p,d in j.get(field,{}).items():
                path=Path(p) if Path(p).is_absolute() else H/p
                assert sha(path)==d,path
    full=read(H/'data/full-source-plan.json');execution=read(H/'data/full-execution-plan.json')
    assert full['module_count']==execution['module_count']==342
    assert full['full_segments']==878 and full['source_bytes']==36831638
    assert set(full['module_order'])==set(execution['module_order'])
    assert execution['module_order'][-1]=='ReplayUnsat150'
    assert not (H/'data/ReplayUnsat150-audit.json').exists()
    for a in full['artifacts']:assert sha(H/a['path'])==a['sha256']
    archive=read(H/'data/source-archives.json');assert archive['status']=='PASS_BYTE_VERIFIED_FULL_SOURCE_ARCHIVE'
    archived=set()
    for a in archive['archives']:
        assert sha(R/a['path'])==a['sha256']
        for x in a['members']:
            assert sha(R/x['path'])==x['sha256'];archived.add((R/x['path']).resolve())
    assert len(archived)==342
    serials=list((H/'data').glob('serialization-*.json'));assert len(serials)==2
    for p in serials:
        j=read(p);assert j['status']=='RESUMED' and j['resume_return_code']==0 and j['transfer_exit_code']==0
        assert j['replay_pid']==15228
    paper=read(H/'data/paper-source-review.json');assert paper['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
    assert sha(R/'paper/snake9_research.tex')==paper['source_sha256']
    assert sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==paper['source_sha256']
    progress=(Q/'replay/data/full-replay-progress.json').read_bytes();live=json.loads(progress)
    assert live['status']=='RUNNING' and live['pid']==15228
    for p,key in [('scripts/run_full_replay.py','driver_sha256'),('scripts/check_full_replay.py','checker_sha256'),('replay/data/full-execution-plan.json','plan_sha256')]:assert sha(Q/p)==live[key]
    cmd='Get-CimInstance Win32_Process -Filter "ProcessId=15228" | Select-Object ProcessId,CommandLine,CreationDate | ConvertTo-Json -Compress'
    proc=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
    assert proc['ProcessId']==15228 and 'run_full_replay.py' in proc['CommandLine']
    assert all(proc['CreationDate']==read(p)['replay_process']['CreationDate'] for p in serials)
    snapshot=H/'data/live-replay147-snapshot.json';snapshot.write_bytes(progress)
    prior=read(P/'data/checkpoint.json');protected=prior['protected_unrelated_files_sha256']
    for p,d in protected.items():assert sha(R/p)==d,p
    verification=dict(status='PASS_INITIAL_TREE_AND_FIRST32_012032_REPLAY_SEGMENTS',
        pilot_completion_sha256=sha(H/'data/pilot-completion.json'),first_group_completion_sha256=sha(H/'data/first-group-completion.json'),
        checked_modules=49,axiom_reports=153,total_modules=342,checked_segments=32,total_segments=878,
        deductions_checked=3728,references_checked=195386,full_Lean_replay_complete=False,
        unconditional012032_share16_complete=False,new_global_upper_bound=False,
        independent_review_sha256=sha(review),archive_receipt_sha256=sha(H/'data/source-archives.json'),
        active_replay_session=67526,active_replay_process=proc,active147_modules_observed=len(live['checked_modules']),
        live147_snapshot_sha256=sha(snapshot),paper_sha256=paper['source_sha256'],pdf_rebuilt=False,
        metadata_note='The source plan preserves an older regeneration filename. The correct151 command is documented; no generated source or accepted plan was changed.')
    (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
    checkpoint=dict(status=verification['status'],goal_status='ACTIVE',round_status='PROGRESS',base_commit=base,
        verification_sha256=sha(H/'data/verification.json'),prior_checkpoint_sha256=sha(P/'data/checkpoint.json'),
        current_interval=[191,235],interval_scope='Maintained contributor upper theorem; complete independent rebuild pending.',
        conditional234_other_premises_unchanged=True,
        selected_next_task='Prioritize remaining012032 full replay with a guarded controller holding/resuming the existing147 coordinator. After342 modules pass, audit and compose the checked150 actual-snake implication.',
        active_replay_session=67526,active_replay_pid=15228,live_snapshot_is_observation_only=True,
        accepted151_modules=49,total151_modules=342,live151_progress_excluded_from_manifest=True,
        unconditional012032_share16_complete=False,unconditional012301_share16_complete=False,
        full_paper_revision_last=146,full_paper_revision_next=156,paper_sha256=paper['source_sha256'],pdf_rebuilt=False,
        protected_unrelated_files_sha256=protected)
    (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
    chosen=set();mutable=H/'data/full-replay-progress.json'
    for folder,dirs,files in os.walk(H):
        dirs[:]=[d for d in dirs if not d.startswith('build') and d!='__pycache__']
        for name in files:
            p=Path(folder)/name
            if p in [manifest,mutable] or p.resolve() in archived or p.suffix in ['.olean','.ilean','.pending','.tmp','.lock'] or name=='stage-paths.nul':continue
            chosen.add(p)
    chosen.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
        'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
    assert mutable not in chosen
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(chosen)]
    manifest.write_text(json.dumps(dict(status='EXACT151_PUBLICATION_MANIFEST',files=rows),indent=2)+'\n',encoding='utf-8')
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
    child=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for path in paths:
        child.stdin.write((':'+path+'\n').encode());child.stdin.flush()
        header=child.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob',header
        left=int(header[2]);d=hashlib.sha256()
        while left:
            data=child.stdout.read(min(left,1048576));assert data;d.update(data);left-=len(data)
        assert child.stdout.read(1)==b'\n' and d.hexdigest()==sha(R/path),path
    child.stdin.close();assert child.wait()==0
print(json.dumps(dict(status='PASS_EXACT151_PUBLICATION_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),
    staged_checked='--stage' in sys.argv or '--check-staged' in sys.argv)))
