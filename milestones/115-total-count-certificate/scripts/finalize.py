"""Freeze a dated research checkpoint while preserving both live Lean batches."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/checkpoint.json').exists()
def save(path,obj):
    path=HERE/path;assert not path.exists();path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8')
def observe(base):
    state=read(base/'data/batch-progress.json');assert state['status']=='RUNNING'
    command=f'Get-Process -Id {int(state["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName,StartTime | ConvertTo-Json -Compress'
    process=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True))
    assert process['Id']==state['pid'] and process['ProcessName']=='python'
    return dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=state)
live=observe(HERE);oldbase=ROOT/'milestones/104-complete-potential-batch';oldlive=observe(oldbase)
save('data/total-batch-observation.json',live);save('data/potential-batch-observation.json',oldlive)
extra=[];pins={};modules=[];audits=[]
for item in live['state']['checked_modules']:
    name=item['module'];rp=HERE/'data'/(name+'-audit.json');r=read(rp)
    assert sha(rp)==item['receipt_sha256'] and r['status']=='PASS_TOTAL_COUNT_MODULE' and r['exit_code']==0 and not r['timeout']
    src=HERE/'lean'/(name.replace('.','/')+'.lean');obj=HERE/'build'/(name.replace('.','/')+'.olean')
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(obj)==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'};audits.append(a)
    pins.update(r['dependencies']);modules.append(dict(module=name,receipt_sha256=sha(rp)))
    for p in [rp,HERE/r['source_snapshot'],(HERE/r['source_snapshot']).parent/'checker.py.txt',HERE/r['log'],
              (HERE/r['log']).with_name((HERE/r['log']).stem+'-record.json')]:
        if p.exists():extra.append(p)
for p,h in pins.items():assert sha(Path(p))==h,p
assert any(m['module']=='Refined115.LocalWindowSat.Total310' for m in modules)
assert any(m['module']=='Refined115.LocalWindowUnsat.Total310.Check1' for m in modules)
assert not any(m['module']=='ActualTotal115' for m in modules)
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','--','milestones/104-complete-potential-batch'],cwd=ROOT,text=True).splitlines())
for item in oldlive['state']['selected']:
    name=item['module'];rp=oldbase/'data'/(name+'-audit.json');r=read(rp)
    assert sha(rp)==item['receipt_sha256'] and r['status']=='PASS_COMPLETE_BATCH_MODULE' and r['exit_code']==0
    assert sha(oldbase/'lean'/(name+'.lean'))==r['source_sha256']==sha(oldbase/r['source_snapshot'])
    assert sha(oldbase/'build'/(name+'.olean'))==r['olean_sha256'] and sha(oldbase/r['log'])==r['log_sha256']
    for p in [rp,oldbase/r['source_snapshot'],(oldbase/r['source_snapshot']).parent/'checker.py.txt',oldbase/r['log']]:
        if p.relative_to(ROOT).as_posix() not in tracked:extra.append(p)
for label,base,stem in [('total',HERE,'batch-console'),('potential',ROOT/'milestones/114-total-count-pressure','resumed-batch')]:
    for stream in ['stdout','stderr']:
        source=base/'logs'/(stem+'.'+stream+'.log');target=HERE/'logs'/(label+'-batch-'+stream+'-snapshot.txt')
        assert not target.exists();target.write_bytes(source.read_bytes());extra.append(target)
save('data/additional-evidence.json',[p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
prior=ROOT/'milestones/114-total-count-pressure/data/checkpoint.json';previous=read(prior)
paper=ROOT/'paper/snake9_research.tex';assert sha(paper)==previous['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
evidence=['data/replay-core1.json','data/total-plan.json','data/total-semantics-plan.json','data/probe-audit.json',
          'data/witness-audit.json','data/graph-cycle-audit.json','data/universal-cycle-audit.json',
          'data/middle345-total22/results.json','data/universal345-total21/results.json','data/universal345-total22/results.json',
          'data/large-artifact-archives.json','data/total-batch-observation.json','data/potential-batch-observation.json',
          'audit/semantic-pilot-review.md','audit/graph-review.md','audit/universal-graph-review.md','audit/final-review.md','mathematical-note.md']
assert read(HERE/'data/replay-core1.json')['status']=='NATIVE_REFINED_CONTRADICTION_REPLAYED_LEAN_PENDING'
assert read(HERE/'data/probes/012345-total22-long.json')['status']=='UNSAT_UNCERTIFIED'
assert read(HERE/'data/probes/012345-total23.json')['status']=='SAT_LOCAL_WITNESS'
summary=dict(status='PASS_CONCRETE_SEMANTICS_NATIVE_EXPORT_AND_CONDITIONAL_GRAPH_REFINEMENT',
    modules=modules,theorem_audits=audits,new_mathematical_definitions=0,
    selected_proof=dict(lemmas=287753,hints=16816989,input_clauses=5114,used_input_clauses=5067),
    total_modules=1397,checked_modules=len(modules),full_lean_contradiction_checked=False,
    local_candidate=dict(directions=[0,1,2,3,4,5],sum_lower=23,negative_certificate_checked=False,
                         local_witness_counts=[6,3,6,2,6],local_witness_components=[43,27,24,9,1,1]),
    source_files_sha256={p:sha(HERE/p) for p in evidence},
    scope='Concrete semantics and a checked contradiction prefix; full Lean replay continues. Native distinct-direction candidate, independently verified local controls and conditional finite graph comparisons. No new global upper bound.')
save('data/proof-summary.json',summary)
refs={name:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',name],cwd=ROOT,text=True).strip() for name in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
checkpoint=dict(status='PASS_PROGRESS_WITH_TWO_LIVE_LEAN_BATCHES',previous_goal_turn='progress',recorded_at=live['recorded_at'],
    prior_checkpoint=prior.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),checked_modules=len(modules),total_modules=1397,
    full_lean_contradiction_checked=False,new_mathematical_definitions=0,new_global_bound=False,
    maintained_interval=[191,235],conditional_target=234,remaining_reference_entries=1366,
    upper_bound_evidence='Contributor proof and archived audit; complete independent rebuild pending.',
    strongest_new_local_candidate='For six distinct consecutive directions, the five internal counts sum to at least 23.',
    candidate_negative_certificate_checked=False,local_model_positive_witness_verified=True,
    final_finite_means=['6309/13','496'],final_valid_ranges=['7656/13','602'],final_integer_comparisons=[235,234],
    next_priority='Preserve both running batches; finish the 012310 Lean replay. Obtain a checked certificate for the 012345 total-23 candidate, and seek restrictions that affect the replacement cycles. Full paper revision 116 is due next.',
    paper_revision=106,next_paper_revision=116,paper_sha256=sha(paper),git_refs_before_commit=refs,
    scope=summary['scope'])
save('data/checkpoint.json',checkpoint)
text=f'''Milestone 115 reduces the 012310 native certificate to 287,753 deductions
and 16,816,989 propagation hints, and checks its concrete interpretation
in Lean. The complete native export passes simulation. Its sequential
Lean batch has {len(modules)}/1397 checked modules in this process-verified
snapshot; the full contradiction and final actual-snake theorem remain pending.

The new candidate is that five internal counts sum to at least 23 when
the six consecutive directions are distinct. Native tests reject totals
at most 22 after five validated cycle cuts; a verified six-component local
forest attains 23. The negative certificate and complete-snake sharpness
remain unresolved. Simpler end-cap restrictions have explicit local controls.

The final graph means are 6309/13 and 496, with valid ranges 7656/13 and 602.
Integer comparisons remain 235 and conditional 234. The attaining cycles
contain no 012345 window at either placement, so further strengthening
that rule leaves the means unchanged by monotonicity. Even zero potential
range cannot improve these integers at the present means.

The maintained interval remains 191 through 235 edges, with the contributor
evidence and complete independent rebuild obligation preserved. Milestone 104
also remains live. This is a dated snapshot, not permission to restart either
batch. Paper revision 106 is unchanged; full revision 116 is due next.
'''
latest='Latest continuation: [milestone 115](milestones/115-total-count-certificate/README.md) checks concrete count semantics and starts the full Lean refutation batch. A new distinct-direction candidate gives five-count total at least 23. Finite means improve to 6309/13 and remain 496; integer comparisons stay 235 and conditional 234.'
priority='Next research priority: Preserve both live Lean batches, complete the 012310 contradiction, and certify the 012345 total-23 candidate. Further restrictions must affect the saved replacement cycles, which contain no 012345 window. Full paper revision 116 is due next.'
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;body=path.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        body,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,body,count=1,flags=re.M);assert n==1
    body=body.replace('The paper is revision 96 and matches the existing editor source.','At that checkpoint, the paper was revision 96; the current revision is 106.')
    path.write_text(body,encoding='utf-8')
path=ROOT/'milestones/README.md';body=path.read_text(encoding='utf-8');index=body.index('- [Milestone 114:')
assert '- [Milestone 115:' not in body
path.write_text(body[:index]+'- [Milestone 115: concrete count semantics and distinct-direction windows](115-total-count-certificate/README.md). Checked semantics, running Lean contradiction batch, a local total23 candidate and improved finite means; no new integer bound.\n\n'+body[index:],encoding='utf-8')
path=ROOT/'RESEARCH_LEDGER.md';body=path.read_text(encoding='utf-8');assert '## Milestone 115:' not in body
path.write_text(body+'\n\n## Milestone 115: concrete count semantics and distinct-direction windows\n\n'+text,encoding='utf-8')
path=ROOT/'handoff/CURRENT_STATUS.md';body=path.read_text(encoding='utf-8');index=body.index('## Milestone 114 checkpoint')
path.write_text(body[:index]+'## Milestone 115 checkpoint\n\n'+text+'\nEarlier checkpoints below are historical snapshots.\n\n'+body[index:],encoding='utf-8')
for name in ['README.md','NEXT_AGENT_PROMPT.md']:(ROOT/'handoff'/name).write_bytes((HERE/'handoff-templates'/name).read_bytes())
print('FROZEN_CHECKPOINT',len(modules),'/',1397,'potential contexts',oldlive['state']['contexts_checked_by_profile'],flush=True)
