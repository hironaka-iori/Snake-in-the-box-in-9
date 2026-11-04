"""Publish the completed local theorem, checked arithmetic and compiled paper."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/completion-publication-manifest.json'
actual=read(H/'data/actual-snake-completion.json')
assert actual['status']=='PASS_ACTUAL_SNAKE_SHARE17_WITH_COUNT_CONDITIONS'
assert actual['count_conditions_retained'] and not actual['extra_unsat_premise'] and not actual['new_global_upper_bound']
assert read(H/'data/post-replay-recovery.json')['status']=='PASS_DIRECT_FINAL_CHECKS_AFTER_PROCESS_QUERY_ERROR'
assert read(H/'data/paper-source-review.json')['status']=='PASS_COMPLETED_LOCAL_THEOREM_PAPER_SOURCE_AND_COMPILATION'
assert not any((H/'data'/name).exists() for name in ['full-replay-batch.lock','final-continuation.lock','memory-resume.lock'])
range_check=read(H/'analysis/range-lean-check.json');assert range_check['status']=='PASS'
for p,d in range_check['dependencies'].items():assert sha(p)==d,p
assert sha(range_check['log'])==range_check['log_sha256'] and sha(range_check['object'])==range_check['olean_sha256']
protected=read(H/'data/resource-recovery-checkpoint.json')['protected_unrelated_files_sha256']
for p,d in protected.items():assert sha(R/p)==d,p
if not manifest.exists():
    intro='''# Current result: local share 17 completed

The 137-module contradiction replay, 98-module interpretation and final
actual-snake composition are complete. The five local count conditions and
their reversed form remain hypotheses; universal012032 share17 is unproved.
The universal share16 theorem remains available without those restrictions.

Three short range implications have also passed Lean. In the specified
fixed profile with012301 and012340 floors16, the retained fourteen-cycle
keeps the comparison at least235-19/587. This limits this comparison's
ability to reach233; it is no new global upper bound.

Both existing paper sources were updated identically and the built-in
compiler succeeded. Authors and preamble are unchanged. The next full
paper revision is156, with a full review of current claims and historical material.
Read milestones/155-share17-replay/COMPLETION.md, its actual-snake completion
record, and analysis/RANGE_NOTE.md. The maintained interval and conditional
234 obligations retain their documented scope. The optimum remains open.

Historical updates follow.

'''
    docs=['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
          'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']
    for name in docs:
        path=R/name;raw=path.read_bytes();assert not raw.startswith(intro.encode())
        path.write_bytes(intro.encode()+raw)
    note=H/'analysis/RANGE_NOTE.md'
    # Preserve the numerical-review record; record the subsequent Lean acceptance separately.
    addendum='''\n## Subsequent Lean verification\n\nThe three arithmetic statements in this note have now passed Lean with\nonly the permitted standard axioms. See range-lean-check.json for the\nexact hypotheses, source, compiler log and dependency hashes. The graph\nextraction scope and absence of a new global snake bound are unchanged.\n'''
    assert '## Subsequent Lean verification' not in note.read_text(encoding='utf-8')
    old_note=note.read_bytes()
    backup=H/'audit/range-note-before-completion.md';assert not backup.exists()
    backup.write_bytes(old_note)
    revised_note=old_note.decode('utf-8').replace(
        'rechecked; the new arithmetic implication below awaits Lean verification.',
        'rechecked. The three arithmetic implications have now passed Lean.')
    note.write_bytes(revised_note.encode()+addendum.encode())
    completion=H/'COMPLETION.md'
    completion.write_bytes(completion.read_bytes()+b'\n## Subsequent document check\n\nThe saved source compiled successfully in the existing desktop editor.\nThe two paper copies are identical; the preamble, authors and hyperref\nsettings are unchanged. See data/paper-compile.json and\ndata/paper-source-review.json. No page-by-page visual review is claimed.\n')
    cp=H/'data/completion-checkpoint.json';assert not cp.exists()
    checkpoint=dict(status='PASS155_LOCAL_SHARE17_AND_RANGE_ARITHMETIC',
        recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        base_commit=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),
        replay_modules=137,semantic_modules=98,final_composition_modules=1,
        replay_axiom_reports=407,semantic_axiom_reports=100,final_axiom_reports=1,
        range_arithmetic_theorems=3,actual_snake_completion_sha256=sha(H/'data/actual-snake-completion.json'),
        count_conditions_retained=True,universal_share17=False,new_global_upper_bound=False,
        paper_sha256=sha(R/'paper/snake9_research.tex'),paper_compilation_success=True,
        last_full_paper_revision=146,next_full_paper_revision=156,goal_status='ACTIVE',
        protected_unrelated_files_sha256=protected)
    cp.write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8',newline='\n')
    selected={R/p for p in docs+['paper/snake9_research.tex','work/paper156-consistency-review.md',
        'work/after155-potential-plan.md','work/after155-potential-plan.json']}
    for folder,dirs,files in os.walk(H):
        dirs[:]=[d for d in dirs if not d.startswith('build') and d!='__pycache__']
        for name in files:
            p=Path(folder)/name
            if p==manifest or p.suffix in ['.olean','.ilean','.pending','.tmp','.lock','.nul']:continue
            selected.add(p)
    assert all(p.exists() and p.stat().st_size<90_000_000 for p in selected)
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
    manifest.write_text(json.dumps(dict(status='EXACT155_COMPLETION_MANIFEST',files=rows),indent=2)+'\n',encoding='utf-8',newline='\n')
rows=read(manifest)['files']
for row in rows:assert sha(R/row['path'])==row['sha256'],row['path']
paths=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
if '--stage' in sys.argv:
    assert not subprocess.check_output(git+['diff','--cached','--name-only'],cwd=R,text=True).strip()
    plist=H/'data/completion-stage-paths.nul';plist.write_bytes(b'\0'.join(p.encode() for p in paths)+b'\0')
    subprocess.run(git+['add','-f','--pathspec-from-file='+str(plist),'--pathspec-file-nul'],cwd=R,check=True)
if '--stage' in sys.argv or '--check-staged' in sys.argv:
    staged={x.decode() for x in subprocess.check_output(git+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0') if x}
    assert staged<=set(paths),staged-set(paths)
    child=subprocess.Popen(git+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for path in paths:
        child.stdin.write((':'+path+'\n').encode());child.stdin.flush()
        header=child.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob',header
        left=int(header[2]);digest=hashlib.sha256()
        while left:
            data=child.stdout.read(min(left,1048576));assert data;digest.update(data);left-=len(data)
        assert child.stdout.read(1)==b'\n' and digest.hexdigest()==sha(R/path),path
    child.stdin.close();assert child.wait()==0
print(json.dumps(dict(status='PASS_EXACT155_COMPLETION_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows))))
