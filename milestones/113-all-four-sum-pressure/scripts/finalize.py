"""Save the reviewed round and a process-verified observation of the existing batch."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,data):
    p=HERE/'data'/name; assert not p.exists()
    p.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')

assert not (HERE/'data/checkpoint.json').exists()
proof=read(HERE/'data/proof-summary.json')
assert proof['status']=='PASS_PAIR_BUDGET_AND_CONDITIONAL_TRANSFER_LOCAL_LIMITATION'
assert len(proof['modules'])==2 and len(proof['theorem_audits'])==4
assert (HERE/'audit/final-review.md').exists()
for p,digest in proof['source_files_sha256'].items():assert sha(ROOT/p)==digest,p
prior_path=ROOT/'milestones/112-critical-sum-refinement/data/checkpoint.json'
prior=read(prior_path)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==prior['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
family=read(HERE/'data/pair24/results.json')
assert family['edges']==4867866 and family['additional_to_previous_family']==41361

batch=ROOT/'milestones/104-complete-potential-batch'
live=read(batch/'data/batch-progress.json'); assert live['status']=='RUNNING'
raw=subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-Process -Id {int(live["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName,StartTime | ConvertTo-Json -Compress'],text=True)
process=json.loads(raw);assert process['Id']==live['pid'] and process['ProcessName']=='python'
observed=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=live)
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','--','milestones/104-complete-potential-batch'],cwd=ROOT,text=True).splitlines())
extra=[]
for group in live['selected']:
    rp=batch/'data'/(group['module']+'-audit.json'); r=read(rp)
    assert sha(rp)==group['receipt_sha256'] and r['status']=='PASS_COMPLETE_BATCH_MODULE' and r['exit_code']==0
    assert sha(batch/'lean'/(group['module']+'.lean'))==r['source_sha256']==sha(batch/r['source_snapshot'])
    assert sha(batch/r['log'])==r['log_sha256'] and sha(batch/'build'/(group['module']+'.olean'))==r['olean_sha256']
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for p in [rp,batch/r['log'],batch/r['source_snapshot'],(batch/r['source_snapshot']).parent/'checker.py.txt']:
        if p.relative_to(ROOT).as_posix() not in tracked:extra.append(p)
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
      for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
assert refs['HEAD']==refs['origin/main']
counts=live['contexts_checked_by_profile']
summary=f'''On canonical 012034, central caps (5,4,5) appear to force the outer
pair to sum to at least 9. Native UNSAT supports the candidate, but two
30-second proof-generation attempts timed out. Lean checks the geometric
transfer with the local contradiction retained as an explicit premise.
No concrete actual-snake pair inequality is claimed.

Lean also checks that the pair deficit fits the existing shared maximum
credit with capacity 4*a+b<=120. There are two successful modules, four
standard axiom reports and no new mathematical definitions. Eleven local
tests comprise six native UNSAT results, two UNKNOWN results and three
independently verified local witnesses. The witness (6,5,4,5,3) attains
pair sum 9, so the current relaxed assumptions cannot force 10.

The pair hypothesis removes 41,361 further keys beyond milestone 112,
leaving 4,867,866. Both finite comparisons remain unchanged: completed
mean/range 484/557 gives 1103389/4684, with integer floor 235; conditional
496/602 gives 551765/2348, with floor 234. Both assume unproved sum rules.
Replacement cycles have zero applicable deficits, proving coefficient
ceilings 484/496 within this fixed eight-rule family. No new global
numerical snake bound follows.

Both replacement cycles contain a 012310 window with five-count sum 18.
The next bounded test is total at most 18 on that pattern with no extra
count caps. A total lower bound of 19 would remove these cycles; compare
both full profiles to determine whether other attaining cycles survive.

At this saved process-verified observation, milestone 104 was RUNNING with
{counts['completed']}/791 completed and {counts['conditional']}/791 conditional contexts
checked. Its active module was `{live['active']['module']}`. Preserve
that batch and all immutable evidence. The reference union still has
1,366 unresolved entries.

The maintained interval remains 191 through 235 edges, based on the
contributor proof and archived audit, with a full independent rebuild
pending. Conditional 234, the exact optimum and 196 remain unresolved.
Paper revision 106 is unchanged; the next full revision is 116.
'''
latest='Latest continuation: [milestone 113](milestones/113-all-four-sum-pressure/README.md) checks shared pair-credit arithmetic and a conditional geometric transfer. A locally sharp candidate removes 41,361 more graph keys; comparisons remain 235 and conditional 234. Replacement cycles fix the present coefficient ceilings.'
priority='Next research priority: Test total count at most 18 on canonical 012310, without extra count caps. Both replacement cycles contain such a window. Compare a viable restriction on both full profiles before proof export. Preserve milestone 104 and avoid repeated coefficient sweeps within the current eight-rule family.'
updates={}
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name; txt=path.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        txt,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,txt,count=1,flags=re.M);assert n==1
    updates[path]=txt
path=ROOT/'milestones/README.md';txt=path.read_text(encoding='utf-8');i=txt.index('- [Milestone 112:');assert '- [Milestone 113:' not in txt
updates[path]=txt[:i]+'- [Milestone 113: pair-count restriction and local limitations](113-all-four-sum-pressure/README.md). Checked shared pair budget and conditional geometry; locally sharp native candidate removes 41,361 more keys. Comparison integers remain 235 and 234.\n\n'+txt[i:]
path=ROOT/'RESEARCH_LEDGER.md';txt=path.read_text(encoding='utf-8');assert '## Milestone 113:' not in txt
updates[path]=txt+'\n\n## Milestone 113: pair-count restriction and replacement cycles\n\n'+summary+'\n'+priority+'\n'
path=ROOT/'handoff/CURRENT_STATUS.md';txt=path.read_text(encoding='utf-8');i=txt.index('## Milestone 112 checkpoint');assert '## Milestone 113 checkpoint' not in txt
updates[path]=txt[:i]+'## Milestone 113 checkpoint\n\n'+summary+'\nEarlier checkpoint sections below are historical snapshots.\n\n'+txt[i:]
checkpoint=dict(status='PASS_PAIR_BUDGET_CONDITIONAL_TRANSFER_AND_FIXED_FAMILY_LIMITATION',previous_goal_turn='progress',recorded_at=observed['recorded_at'],
    prior_checkpoint=prior_path.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior_path),
    checked_final_modules=2,theorem_axiom_audits=4,new_mathematical_definitions=0,
    pair_budget_lean_checked=True,pair_geometry_with_local_premise_lean_checked=True,
    concrete_pair_contradiction_checked=False,complete_restricted_graph_lean_certificate=False,
    native_probes=dict(UNSAT_UNCERTIFIED=6,UNKNOWN=2,SAT_LOCAL_WITNESS=3),
    native_proof_timeouts=2,conditional_family_graph_keys=4867866,further_keys_removed=41361,
    family_profile_comparisons=[dict(profile='completed',mean='484',range='557',comparison='1103389/4684',integer=235),
        dict(profile='conditional',mean='496',range='602',comparison='551765/2348',integer=234)],
    fixed_family_coefficient_ceilings=[484,496],remaining_reference_entries=1366,
    recovered_reference_indices=prior['recovered_reference_indices'],maintained_interval=[191,235],conditional_target=234,
    exact_optimum_unresolved=True,new_global_bound=False,
    upper_bound_evidence='Contributor proof and archived audit; complete independent rebuild pending.',
    next_test=dict(directions=[0,1,2,3,1,0],bounds=[[0,21]]*5,positions=[0,1,2,3,4],cap=18,status='NOT_RUN'),
    paper_revision=106,next_paper_revision=116,paper_sha256=sha(paper),git_refs_before_commit=refs,
    evidence_sha256={p:sha(HERE/p) for p in ['data/proof-summary.json','data/independent-check.json','audit/final-review.md',
        'mathematical-note.md','data/pair24/results.json','data/interval45454/results.json','data/large-artifact-archives.json']},
    scope='Checked generic pair budget and conditional geometry, native local candidate with matching relaxed witness, and unchanged conditional finite comparisons. No concrete pair theorem or improved numerical snake bound.')
save('batch-observation.json',observed)
checkpoint['batch_observation_sha256']=sha(HERE/'data/batch-observation.json')
save('additional-batch-evidence.json',[p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
for path,txt in updates.items():path.write_text(txt,encoding='utf-8')
for name in ['README.md','NEXT_AGENT_PROMPT.md']:
    (ROOT/'handoff'/name).write_bytes((HERE/'handoff-templates'/name).read_bytes())
save('checkpoint.json',checkpoint)
print(json.dumps(dict(status=checkpoint['status'],batch_counts=counts,additional_batch_files=len(set(extra))),indent=2))
