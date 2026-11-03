"""Validate the exact147 proof boundary and stage only immutable manifest files."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
H=Path(__file__).resolve().parents[1];Q=H/'replay';R=H.parents[1]
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
def pins(j,key='source_files_sha256'):
    for p,d in j.get(key,{}).items():
        p=Path(p);assert sha(p if p.is_absolute() else R/p)==d,p
def receipt(p):
    q=read(p);assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None,p
    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']
    assert sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256'] and sha(folder/'checker.py.txt')==q['checker_sha256']
    pins(q,'dependencies')
    source=Path(q['source']).read_text(encoding='utf-8')
    assert len(q['axioms'])==source.count('#print axioms')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
    return len(q['axioms'])
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
    assert len(sys.argv)==1
    base='eb5270e8d70f8ae2060ffc2ffbb093fdcb0d2f21'
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()==base
    sem=read(H/'data/semantics-completion.json');pins(sem)
    assert sem['status']=='PASS_COMPLETE_CORE_CLAUSE_INTERPRETATION_AND_ASSEMBLY'
    assert (sem['checked_modules'],sem['axiom_reports'],sem['original_core_clauses'])==(113,111,12977)
    pilot=read(Q/'data/pilot-completion.json');pins(pilot)
    assert pilot['status']=='PASS_15BIT_CHECKER_INITIAL_TREE_AND_CHECKPOINT_PILOT'
    assert (pilot['checked_modules'],pilot['axiom_reports'])==(36,116)
    first=read(Q/'data/first-group-completion.json')
    assert first['status']=='PASS_FIRST32_REPLAY_SEGMENTS_AND_CHECKPOINT'
    assert (first['checked_modules'],first['deductions_checked'],first['references_checked'])==(47,8653,195344)
    assert sha(Q/'data/first-group-progress-snapshot.json')==first['progress_snapshot_sha256']
    assert sha(Q/'data/full-execution-plan.json')==first['full_execution_plan_sha256']
    prog=read(Q/'data/full-replay-progress.json')
    assert prog['status']=='PASS_BOUNDED_FULL_REPLAY_PREFIX' and prog['active'] is None
    assert not (Q/'data/full-replay-batch.lock').exists()
    reports=0
    for folder,rows in [(H,sem['receipts']),(Q,first['receipts'])]:
        for x in rows:
            rp=folder/x['receipt'];assert sha(rp)==x['sha256'];reports+=receipt(rp)
    assert reports==260,reports
    print('Verified160 accepted modules and260 axiom reports.',flush=True)
    plans=[H/'data/semantic-plan.json',H/'data/assembly-plan.json',Q/'data/full-source-plan.json',Q/'data/full-execution-plan.json']
    for p in plans:
        plan=read(p);folder=Q if p.is_relative_to(Q) else H
        for x in plan['artifacts']:assert sha(folder/x['path'])==x['sha256']
    native=read(Q/'data/packed-replay.json')
    assert native['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
    assert (native['deductions'],native['hints'],native['final_tree_key'])==(285541,31017505,11657)
    for x in native['artifacts']+native['checkpoints']:assert sha(Q/x['path'])==x['sha256']
    assert sha(H/'audit/full-layout-review147.json')=='fee08589f9c950bdba0cd4f18f6a629a8b15825d09dcc5557c0bfdc077db10ef'
    review=read(H/'audit/full-layout-review147.json')
    assert review['status']=='PASS_BOUNDED_SOURCE_LAYOUT_AND_CHECKED_HELPER_AUDIT'
    archives=read(H/'data/replay-archives.json');assert archives['status']=='PASS_BYTE_VERIFIED_REPLAY_ARCHIVES'
    archived=set()
    for a in archives['archives']:
        assert sha(R/a['path'])==a['sha256']
        for x in a['members']:
            p=R/x['path'];assert p not in archived;archived.add(p)
            assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes']
    assert len(archived)==1953
    print('Verified immutable source plans, packed inputs and archives.',flush=True)
    paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
    pr=read(H/'data/paper-source-review.json');rev=read(H/'data/paper-revision.json')
    assert sha(paper)==sha(editor)==pr['source_sha256']==rev['source_sha256_after']
    assert pr['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS' and pr['new_definitions']==0
    assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before147.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
    comp=read(H/'data/paper-compile.json');assert comp['paper_sha256']==sha(paper)
    payload=json.loads(comp['result']['content'][0]['text'])
    assert payload['kind']=='compile-failed' and 'Compiler helper failed' in payload['diagnostics']['log']
    evidence=[H/'data/semantics-completion.json',Q/'data/pilot-completion.json',Q/'data/first-group-completion.json',
        H/'audit/full-layout-review147.json',H/'data/replay-archives.json',H/'data/paper-source-review.json',H/'data/paper-compile.json']
    verification=dict(status='PASS_COMPLETE_CLAUSE_SEMANTICS_AND_FIRST32_REPLAY_SEGMENTS',
        semantic_modules=113,replay_modules=47,total_checked_modules=160,axiom_reports=260,
        core_clauses=12977,cycle_clauses=6,replay_segments=32,replay_deductions=8653,replay_references=195344,
        full_replay_modules=1789,full_replay_segments=5089,
        full_Lean_replay_complete=False,actual_snake_share16_complete=False,new_global_upper_bound=False,
        paper_sha256=sha(paper),pdf_rebuilt=False,last_full_paper_revision=146,next_full_paper_revision=156,
        evidence_sha256={p.relative_to(H).as_posix():sha(p) for p in evidence})
    (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8',newline='\n')
    checkpoint=dict(status=verification['status'],goal_status='ACTIVE',current_round='PROGRESS',base_commit=base,
        verification_sha256=sha(H/'data/verification.json'),
        prior_checkpoint_sha256=sha(R/'milestones/146-initial-tree-and-paper/data/checkpoint.json'),
        current_interval=[191,235],interval_scope='Maintained contributor upper proof; full independent rebuild pending.',
        selected_next_task='Resume the existing full012301 replay, then compose exact local semantics, coordinate transport and reversal; retain012032 and012340 joint dependencies.',
        immutable_replay_boundary='replay/data/first-group-completion.json',
        live_replay_status_path='replay/data/full-replay-progress.json',live_progress_excluded_from_publication=True,
        no_active_job_at_checkpoint=True,full_replay_may_resume_after_publication=True,
        last_full_paper_revision=146,next_full_paper_revision=156,paper_sha256=sha(paper),pdf_rebuilt=False,
        completed012310_count_proof_do_not_restart=True,
        protected_unrelated_files_sha256={n:sha(R/n) for n in ['.gitignore','milestones/50-three-count-return/excess-screen/data/critical-family.json']})
    (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8',newline='\n')
    selected=set()
    for folder,dirs,files in os.walk(H,followlinks=False):
        dirs[:]=[n for n in dirs if not n.startswith('build') and n!='__pycache__']
        for name in files:
            p=Path(folder)/name
            if p==manifest or p in archived or p==Q/'data/full-replay-progress.json':continue
            if p.suffix in ['.tmp','.pending','.lock','.olean','.ilean'] or name=='stage-paths.nul':continue
            selected.add(p)
    selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
    assert all(x['bytes']<100000000 for x in rows)
    manifest.write_text(json.dumps(dict(status='EXACT_147_PUBLICATION_MANIFEST',files=rows),indent=2)+'\n',encoding='utf-8',newline='\n')
rows=read(manifest)['files']
for x in rows:assert sha(R/x['path'])==x['sha256'] and (R/x['path']).stat().st_size==x['bytes'],x['path']
paths=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
if '--stage' in sys.argv:
    existing=subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0')
    assert not [p for p in existing if p]
    pathlist=H/'data/stage-paths.nul';pathlist.write_bytes(b'\0'.join(p.encode() for p in paths)+b'\0')
    subprocess.run(g+['add','-f','--pathspec-from-file='+str(pathlist),'--pathspec-file-nul'],cwd=R,check=True)
if '--check-staged' in sys.argv or '--stage' in sys.argv:
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
print(json.dumps(dict(status='PASS_EXACT_147_PUBLICATION_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),staged_checked='--check-staged' in sys.argv or '--stage' in sys.argv)))
