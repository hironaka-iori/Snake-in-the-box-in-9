"""Verify the exact conditional transfer checkpoint and stage its manifest."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,datetime,zipfile
H=Path(__file__).resolve().parents[1];R=H.parents[1];Q=R/'milestones/147-countfree-clause-semantics'
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
    base='3177068026105d4321582f179dce7020f029bf59'
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()==base
    done=read(H/'data/transfer-completion.json')
    assert done['status']=='PASS_CONDITIONAL_ACTUAL_SNAKE_SHARE16_TRANSFER'
    assert (done['checked_modules'],done['axiom_reports'])==(16,27)
    assert done['coordinate_and_reversal_transfer_checked'] and not done['unconditional_actual_snake_share16_complete']
    for p,d in done['evidence_sha256'].items():assert sha(H/p)==d,p
    plan=read(H/'data/transfer-plan-v4.json');artifacts={x['module']:x for x in plan['artifacts']}
    known="/- A snake's length is its number of edges. No optimality axiom is declared. -/"
    for x in done['receipts']:
        p=H/x['receipt'];q=read(p);assert sha(p)==x['sha256']
        assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
        assert sha(q['source'])==q['source_sha256']==artifacts[x['module']]['sha256']
        assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
        folder=Path(q['log']).parent
        assert sha(folder/'source.lean.txt')==q['source_sha256'] and sha(folder/'checker.py.txt')==q['checker_sha256']
        for p,d in q['dependencies'].items():assert sha(p)==d,p
        source=Path(q['source']).read_text(encoding='utf-8')
        assert len(q['axioms'])==source.count('#print axioms')
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.replace(known,''))
        assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
    reused=read(H/'data/reused-data-object.json');assert not reused['fresh_compilation']
    for p,d in reused['source_files_sha256'].items():assert sha(p)==d,p
    ar=read(H/'data/inherited-data-archive.json');assert sha(R/ar['path'])==ar['sha256']
    with zipfile.ZipFile(R/ar['path']) as z:
        for x in ar['members']:assert hashlib.sha256(z.read(x['path'])).hexdigest()==x['sha256']
    for row in plan['artifacts']:assert sha(H/row['path'])==row['sha256']
    assert not any((H/'data').glob('*batch.lock'))
    for x in done['serialization_records']:
        p=H/x['path'];assert sha(p)==x['sha256'];j=read(p)
        assert j['status']=='RESUMED' and j['resume_return_code']==0 and j['replay_pid']==15228
    print('Verified16 accepted module checks,27 axiom reports and the inherited data boundary.',flush=True)
    complete=read(H/'data/completion-plan.json');assert not complete['checked']
    assert not (H/'data/ShareComplete148-audit.json').exists() and not (H/'build/ShareComplete148.olean').exists()
    for x in complete['artifacts']:assert sha(H/x['path'])==x['sha256']
    assert read(H/'data/completion-guard-test.json')['status']=='PASS_WAITING_GUARD'
    paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
    pr=read(H/'data/paper-source-review.json');rev=read(H/'data/paper-revision.json')
    assert pr['status']=='PASS_CONDITIONAL_TRANSFER_PAPER_SOURCE_CHECKS'
    assert sha(paper)==sha(editor)==pr['source_sha256']==rev['source_sha256_after']
    before=(H/'audit/paper-before148.tex.txt').read_bytes();assert hashlib.sha256(before).hexdigest()==rev['source_sha256_before']
    assert before.split(b'\\begin{document}',1)[0]==paper.read_bytes().split(b'\\begin{document}',1)[0]
    assert pr['new_definitions']==0
    comp=read(H/'data/paper-compile.json');assert comp['paper_sha256']==sha(paper)
    payload=json.loads(comp['result']['content'][0]['text']);assert payload['kind']=='compile-failed' and 'Compiler helper failed' in payload['diagnostics']['log']
    livepath=Q/'replay/data/full-replay-progress.json';raw=livepath.read_bytes();live=json.loads(raw)
    assert live['status']=='RUNNING' and live['pid']==15228
    cmd='Get-CimInstance Win32_Process -Filter "ProcessId=15228" | Select-Object ProcessId,CommandLine,CreationDate | ConvertTo-Json -Compress'
    proc=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
    assert proc['ProcessId']==15228 and 'run_full_replay.py' in proc['CommandLine']
    assert proc['CreationDate']==done['live_replay_process']['CreationDate']
    snapshot=H/'data/live-replay-snapshot.json';snapshot.write_bytes(raw)
    verification=dict(status='PASS_CONDITIONAL_TRANSFER_AND_SAVED_REPLAY_CONTINUATION',
        transfer_modules=16,axiom_reports=27,coordinate_and_reversal_transfer_checked=True,
        inherited_data_reused=True,inherited_data_freshly_rebuilt=False,
        core_contradiction_still_required=True,unconditional_share16_complete=False,new_global_upper_bound=False,
        transfer_receipt_sha256=sha(H/'data/transfer-completion.json'),
        pending_composition_source_sha256=sha(H/'lean/ShareComplete148.lean'),
        live_replay_session=67526,live_replay_process=proc,live_snapshot_sha256=sha(snapshot),
        live_replay_modules_observed=len(live['checked_modules']),
        paper_sha256=sha(paper),pdf_rebuilt=False,last_full_paper_revision=146,next_full_paper_revision=156)
    (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8',newline='\n')
    checkpoint=dict(status=verification['status'],goal_status='ACTIVE',current_round='PROGRESS',base_commit=base,
        verification_sha256=sha(H/'data/verification.json'),prior_checkpoint_sha256=sha(Q/'data/checkpoint.json'),
        selected_next_task='Continue the same full147 replay; audit the completed contradiction, then check148 ShareComplete148. The conditional actual-snake transfer is complete.',
        current_interval=[191,235],interval_scope='Maintained contributor upper proof; complete independent rebuild pending.',
        active_replay_session=67526,active_replay_pid=15228,
        live_snapshot_is_observation_only=True,unconditional_share16_complete=False,
        last_full_paper_revision=146,next_full_paper_revision=156,paper_sha256=sha(paper),pdf_rebuilt=False,
        protected_unrelated_files_sha256={n:sha(R/n) for n in ['.gitignore','milestones/50-three-count-return/excess-screen/data/critical-family.json']})
    (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8',newline='\n')
    selected=set()
    for folder,dirs,files in os.walk(H,followlinks=False):
        dirs[:]=[n for n in dirs if not n.startswith('build') and n!='__pycache__']
        for name in files:
            p=Path(folder)/name
            if p==manifest or p.suffix in ['.tmp','.pending','.lock','.olean','.ilean'] or name=='stage-paths.nul':continue
            selected.add(p)
    selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
    assert all(x['bytes']<100000000 for x in rows)
    manifest.write_text(json.dumps(dict(status='EXACT_148_PUBLICATION_MANIFEST',files=rows),indent=2)+'\n',encoding='utf-8',newline='\n')
rows=read(manifest)['files']
for x in rows:assert sha(R/x['path'])==x['sha256'] and (R/x['path']).stat().st_size==x['bytes'],x['path']
paths=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
if '--stage' in sys.argv:
    assert not subprocess.check_output(g+['diff','--cached','--name-only'],cwd=R,text=True).strip()
    plist=H/'data/stage-paths.nul';plist.write_bytes(b'\0'.join(p.encode() for p in paths)+b'\0')
    subprocess.run(g+['add','-f','--pathspec-from-file='+str(plist),'--pathspec-file-nul'],cwd=R,check=True)
if '--stage' in sys.argv or '--check-staged' in sys.argv:
    staged={x.decode() for x in subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0') if x}
    assert staged==set(paths),(staged-set(paths),set(paths)-staged)
    proc=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for path in paths:
        proc.stdin.write((':'+path+'\n').encode());proc.stdin.flush()
        header=proc.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob',header
        left=int(header[2]);d=hashlib.sha256()
        while left:
            b=proc.stdout.read(min(1048576,left));assert b;d.update(b);left-=len(b)
        assert proc.stdout.read(1)==b'\n' and d.hexdigest()==sha(R/path),path
    proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_EXACT148_PUBLICATION_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),staged_checked='--stage' in sys.argv or '--check-staged' in sys.argv)))
