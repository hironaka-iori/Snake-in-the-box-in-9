"""Save this completed research round and an immutable live-batch observation."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,data):(HERE/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists() and not (HERE/'data/check.lock').exists()
proof=read(HERE/'data/proof-summary.json')
assert proof['status']=='PASS_ACTUAL_SUM_THEOREM_AND_SHARED_BUDGET'
assert len(proof['modules'])==40 and len(proof['theorem_audits'])==20
assert sha(HERE/'audit/final-review.md')=='b9b2e33a52bb52cfe6b12d6befdafe15bc96fb2d6e6eef2aca136dadd90e6bf5'
prior_path=ROOT/'milestones/111-critical-count-intervals/data/checkpoint.json';prior=read(prior_path)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==prior['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
family=read(HERE/'data/expanded24/results.json')
assert family['edges']==4909227 and family['additional_removed']==33362
assert [(p['mean'],p['range']) for p in family['profiles']]==[('484','557'),('496','602')]
batch=ROOT/'milestones/104-complete-potential-batch';live=read(batch/'data/batch-progress.json')
assert live['status']=='RUNNING'
raw=subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-Process -Id {int(live["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName,StartTime | ConvertTo-Json -Compress'],text=True)
process=json.loads(raw);assert process['Id']==live['pid'] and process['ProcessName']=='python'
observed=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=live)
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','--','milestones/104-complete-potential-batch'],cwd=ROOT,text=True).splitlines())
extra=[]
for group in live['selected']:
    rp=batch/'data'/(group['module']+'-audit.json');r=read(rp)
    assert sha(rp)==group['receipt_sha256'] and r['status']=='PASS_COMPLETE_BATCH_MODULE' and r['exit_code']==0
    assert sha(batch/'lean'/(group['module']+'.lean'))==r['source_sha256']==sha(batch/r['source_snapshot'])
    assert sha(batch/r['log'])==r['log_sha256'] and sha(batch/'build'/(group['module']+'.olean'))==r['olean_sha256']
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for p in [rp,batch/r['log'],batch/r['source_snapshot'],(batch/r['source_snapshot']).parent/'checker.py.txt']:
        if p.relative_to(ROOT).as_posix() not in tracked:extra.append(p)
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
assert refs['HEAD']==refs['origin/main']
counts=live['contexts_checked_by_profile']
summary=f'''A new actual-snake theorem proves that on canonical direction pattern
012314, middle count at most 2 forces the four outer counts to sum to at
least 19. The concrete counter semantics, complete contradiction and
geometric transfer pass Lean without a collective catalogue premise.
The proof uses 3,306 clauses, 7,020 deductions and 367,588 hints after
a verified permutation of 1,718 active variables. Independent replay
and reconstruction pass. This round has 40 successful modules and 20
printed standard axiom reports, with no new mathematical definitions.

Lean also checks a shared budget for outer-four and total-five deficits.
Fixed coefficients satisfy 4*a+b<=120; take the maximum of the weighted
alternative deficits. The clipped-count boundary contribution remains
21, or 2,520 after scaling. Actual local lower bounds remain explicit
hypotheses in the generic budget theorem.

The final seven-rule conditional experiment leaves 4,909,227 graph keys.
Balanced coefficients (24,24) give completed mean 484/range 557 and
comparison 1103389/4684, with integer floor 235. The conditional profile
retains mean 496/range 602 and floor 234. Surviving zero-deficit cycles
show these means are ceilings for every nonnegative coefficient choice
within the fixed family. Balanced coefficients attain both ceilings.
Lean-checked arithmetic shows that smaller nonnegative potential ranges
alone cannot exclude 235 or 234 at these slopes.

Six local witnesses independently rule out other strengthenings within
the relaxed radius-four model; they are not complete snakes. The next
useful target is the all-4 configuration on 012034, followed by a broader
count-sum inequality if it is impossible. The relevant stronger sum
probes are UNKNOWN. The separate 30-second proof-generation timeout is
preserved; its partial LRAT is not a checked certificate.

At the saved process-verified observation, milestone 104 was RUNNING with
{counts['completed']}/791 completed and {counts['conditional']}/791 conditional contexts
checked. Its active module was `{live['active']['module']}`. Preserve
that batch. The reference union still has 1,366 unresolved entries.

The maintained range remains 191 through 235 edges, based on the
contributor proof and archived audit with full independent rebuilding
pending. Other sum hypotheses, graph-oriented guards and complete global
integration remain pending. No improved numerical snake bound is claimed.
Conditional 234, the exact optimum and 196 remain unresolved. Paper
revision 106 is unchanged; the next full revision is 116.
'''
latest='Latest continuation: [milestone 112](milestones/112-critical-sum-refinement/README.md) proves an actual count-sum theorem and a shared charging budget. The expanded conditional graph reaches completed mean 484; integer comparisons remain 235 and conditional 234. Zero-deficit cycles rule out further coefficient improvement within this fixed family.'
priority='Next research priority: Test the exact all-4 configuration on 012034, then seek a stronger family sum inequality if it is impossible. Compare every viable candidate on both full profiles. Do not repeat coefficient sweeps for the current seven rules; preserve the running milestone 104 batch and all pending proof evidence.'
updates={}
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;txt=path.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        txt,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,txt,count=1,flags=re.M);assert n==1
    updates[path]=txt
path=ROOT/'milestones/README.md';txt=path.read_text(encoding='utf-8');i=txt.index('- [Milestone 111:');assert '- [Milestone 112:' not in txt
updates[path]=txt[:i]+'- [Milestone 112: actual sum theorem and shared budget](112-critical-sum-refinement/README.md). Checked geometry and counter semantics; completed finite mean 484 with an exact coefficient ceiling. Integer comparisons remain 235 and 234.\n\n'+txt[i:]
path=ROOT/'RESEARCH_LEDGER.md';txt=path.read_text(encoding='utf-8');assert '## Milestone 112:' not in txt
updates[path]=txt+'\n\n## Milestone 112: actual sum theorem and fixed-family ceiling\n\n'+summary+'\n'+priority+'\n'
path=ROOT/'handoff/CURRENT_STATUS.md';txt=path.read_text(encoding='utf-8');i=txt.index('## Milestone 111 checkpoint');assert '## Milestone 112 checkpoint' not in txt
updates[path]=txt[:i]+'## Milestone 112 checkpoint\n\n'+summary+'\nEarlier checkpoint sections below are historical snapshots.\n\n'+txt[i:]
templates={ROOT/'handoff'/name:(HERE/'handoff-templates'/name).read_bytes() for name in ['README.md','NEXT_AGENT_PROMPT.md']}
checkpoint=dict(status='PASS_ACTUAL_SUM_AND_SHARED_BUDGET_FIXED_FAMILY_OPTIMUM',previous_goal_turn='progress',recorded_at=observed['recorded_at'],
    prior_checkpoint=prior_path.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior_path),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),final_review_sha256=sha(HERE/'audit/final-review.md'),
    mathematical_note_sha256=sha(HERE/'mathematical-note.md'),family_result_sha256=sha(HERE/'data/expanded24/results.json'),
    archives_sha256=sha(HERE/'data/large-artifact-archives.json'),checked_final_modules=40,theorem_axiom_audits=20,new_mathematical_definitions=0,
    actual_snake_checked=True,directions=[0,1,2,3,1,4],middle_upper=2,outer_lower=19,
    shared_excess_arithmetic_lean_checked=True,sum_counter_semantics_lean_checked=True,comparison_barriers_lean_checked=True,
    graph_orientation_guards_lean_checked=False,other_sum_hypotheses_lean_checked=False,complete_restricted_graph_lean_certificate=False,
    conditional_family_graph_keys=4909227,conditional_family_total_exclusions=37781,
    family_profile_comparisons=[dict(profile='completed',mean='484',range='557',comparison='1103389/4684',integer=235),
        dict(profile='conditional',mean='496',range='602',comparison='551765/2348',integer=234)],
    fixed_family_coefficient_ceilings=[484,496],remaining_reference_entries=1366,recovered_reference_indices=prior['recovered_reference_indices'],
    maintained_interval=[191,235],conditional_target=234,exact_optimum_unresolved=True,
    upper_bound_evidence='Contributor proof and archived audit; complete independent rebuild pending.',
    paper_revision=106,next_paper_revision=116,paper_sha256=sha(paper),git_refs_before_commit=refs,
    scope='One actual-snake sum theorem, shared excess arithmetic and a conditional finite-model optimum for coefficient choices. No improved numerical snake bound; other sum hypotheses and complete global integration remain pending.')
save('batch-observation.json',observed)
checkpoint['batch_observation_sha256']=sha(HERE/'data/batch-observation.json')
save('additional-batch-evidence.json',[p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
for path,txt in updates.items():path.write_text(txt,encoding='utf-8')
for path,raw in templates.items():path.write_bytes(raw)
save('checkpoint.json',checkpoint)
print(json.dumps(dict(status=checkpoint['status'],batch_counts=counts,additional_batch_files=len(set(extra))),indent=2))
