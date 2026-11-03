"""Audit and optionally stage the exact milestone150 checkpoint."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
Q=R/'milestones/147-countfree-clause-semantics'
P=R/'milestones/149-share-credit-tradeoff'
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
    base='43a70d91dd978527b1cc4de7110205fe9822c693'
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()==base
    sem=read(H/'data/semantics-completion.json')
    assert sem['status']=='PASS_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE16'
    assert sem['checked_modules']==112 and sem['axiom_reports']==112
    assert sem['core_unsat_is_explicit_premise'] and not sem['unconditional_actual_snake_share16_complete']
    for p,d in sem['source_files_sha256'].items():assert sha(R/p)==d,p
    for row in sem['receipts']:
        receipt=H/row['receipt'];assert sha(receipt)==row['sha256'];j=read(receipt)
        assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
        for name,digest in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
            assert sha(j[name])==j[digest]
        for p,d in j['dependencies'].items():assert sha(p)==d,p
    reviewpins={
        'countfree-core-review.json':'d70d02635f61bf578f4eddf25234125c20c2c59a3d1d14cd095d38fa92046ae4',
        'countfree-core-review.md':'c6c54fd683f20d303558e91db4ef372b97fd2e89ef537a7e8eb9d48aedf07b59',
        'transport-review.json':'e705a688230c84116ec26e25a6fad5f2ad0bab89e09f5f7a832adf14e3c97eec',
        'transport-review.md':'32a055549f900d96f87e064ba5a633cf45f092b570da67699b6ac6a9dfc7c817',
        'actual-event-bridge.md':'e8d8080b31ba3cf2b59a8e7870536757101b88dc4540b55b2e1b33941c8a8d59',
        'conditional-transfer-review.md':'5c0af88bc18faf0772a048df1eddc3115330e6cfbb92f0736feb9e53673dbfe0',
        'conditional-transfer-review.json':'6f3f37fe394c03d3a00a9640817e9012cbdcdf056f9282585bbe79410a0e54b1'}
    for name,d in reviewpins.items():assert sha(H/'audit'/name)==d,name
    for name in ['countfree-core-review.json','transport-review.json']:
        j=read(H/'audit'/name)
        for field in ['pins','encoder_dependency_pins','native_replay_implementation_pins']:
            for p,d in j.get(field,{}).items():assert sha(R/p)==d,p
    native=read(H/'work/highpair16/native-replay.json')
    assert native['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
    assert (native['deductions'],native['hints'],native['core_clauses'],native['actual_pair_clauses_used'])==(58182,5350080,13655,0)
    packed=read(H/'replay/data/packed-replay.json')
    assert packed['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
    pilot=read(H/'replay/data/pilot-source-plan.json')
    assert pilot['status']=='SOURCE_PREPARED_UNCHECKED' and pilot['module_count']==38
    for x in pilot['artifacts']:assert sha(H/'replay'/x['path'])==x['sha256']
    assert not (H/'replay/data/pilot-completion.json').exists()
    archive=read(H/'data/input-archives.json');archived=set()
    assert archive['status']=='PASS_BYTE_VERIFIED_NATIVE_AND_TRANSPORT_ARCHIVES'
    for a in archive['archives']:
        assert sha(R/a['path'])==a['sha256']
        for x in a['members']:
            assert sha(R/x['path'])==x['sha256'];archived.add((R/x['path']).resolve())
    assert len(archived)==archive['member_count']==66
    serial=read(next((H/'data').glob('serialization-*.json')))
    assert serial['status']=='RESUMED' and serial['resume_return_code']==0 and serial['transfer_exit_code']==0
    paper=read(H/'data/paper-source-review.json')
    assert paper['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
    assert sha(R/'paper/snake9_research.tex')==paper['source_sha256']
    assert sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==paper['source_sha256']
    progress=(Q/'replay/data/full-replay-progress.json').read_bytes();live=json.loads(progress)
    assert live['status']=='RUNNING' and live['pid']==15228
    for p,key in [('scripts/run_full_replay.py','driver_sha256'),('scripts/check_full_replay.py','checker_sha256'),('replay/data/full-execution-plan.json','plan_sha256')]:
        assert sha(Q/p)==live[key]
    cmd='Get-CimInstance Win32_Process -Filter "ProcessId=15228" | Select-Object ProcessId,CommandLine,CreationDate | ConvertTo-Json -Compress'
    proc=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
    assert proc['ProcessId']==15228 and 'run_full_replay.py' in proc['CommandLine']
    assert proc['CreationDate']==serial['replay_process']['CreationDate']
    snapshot=H/'data/live-replay-snapshot.json';snapshot.write_bytes(progress)
    protected=read(P/'data/checkpoint.json')['protected_unrelated_files_sha256']
    for p,d in protected.items():assert sha(R/p)==d,p
    verification=dict(status='PASS_EXACT_COUNTFREE_CORE_AND_CONDITIONAL_SHARE_TRANSFER',
        semantics_completion_sha256=sha(H/'data/semantics-completion.json'),
        native_deductions=58182,native_hints=5350080,core_clauses=13655,additional_pair_assumption=False,
        checked_semantic_and_transfer_modules=112,axiom_reports=112,
        full_numerical_transport_complete=True,pilot_Lean_checked=False,full_Lean_replay_complete=False,
        unconditional012032_share16_complete=False,new_global_upper_bound=False,
        frozen_audit_sha256=reviewpins,archive_receipt_sha256=sha(H/'data/input-archives.json'),
        active_replay_session=67526,active_replay_process=proc,active_modules_observed=len(live['checked_modules']),
        live_snapshot_sha256=sha(snapshot),paper_sha256=paper['source_sha256'],pdf_rebuilt=paper['pdf_rebuilt'])
    (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
    checkpoint=dict(status=verification['status'],goal_status='ACTIVE',round_status='PROGRESS',base_commit=base,
        verification_sha256=sha(H/'data/verification.json'),prior_checkpoint_sha256=sha(P/'data/checkpoint.json'),
        current_interval=[191,235],interval_scope='Maintained contributor upper theorem; complete independent rebuild pending.',
        conditional234_other_premises_unchanged=True,
        selected_next_task='Continue same147 full replay and guarded148 composition. Next new012032 task: bounded initial-tree/prefix pilot, with no overlapping Lean compiler.',
        active_replay_session=67526,active_replay_pid=15228,live_snapshot_is_observation_only=True,
        unconditional012032_share16_complete=False,unconditional012301_share16_complete=False,
        full_paper_revision_last=146,full_paper_revision_next=156,paper_sha256=paper['source_sha256'],
        pdf_rebuilt=paper['pdf_rebuilt'],protected_unrelated_files_sha256=protected)
    (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
    chosen=set()
    for folder,dirs,files in os.walk(H):
        dirs[:]=[d for d in dirs if not d.startswith('build') and d not in ['work','__pycache__']]
        for name in files:
            p=Path(folder)/name
            if p==manifest or p.resolve() in archived or p.suffix in ['.olean','.ilean','.pending','.tmp','.lock'] or name=='stage-paths.nul':continue
            chosen.add(p)
    chosen.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
        'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(chosen)]
    manifest.write_text(json.dumps(dict(status='EXACT150_PUBLICATION_MANIFEST',files=rows),indent=2)+'\n',encoding='utf-8')
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
print(json.dumps(dict(status='PASS_EXACT150_PUBLICATION_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),
    staged_checked='--stage' in sys.argv or '--check-staged' in sys.argv)))
