"""Save a milestone checkpoint and a live-process-verified observation of batch104."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,data):(HERE/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists() and not (HERE/'data/check.lock').exists()
proof=read(HERE/'data/proof-summary.json');assert proof['status']=='PASS_NEW_LOCAL_COUNT_EXCLUSION'
assert (HERE/'audit/final-review.md').exists()
prior_path=ROOT/'milestones/109-relaxed-graph-test/data/checkpoint.json';prior=read(prior_path)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==prior['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
batch=ROOT/'milestones/104-complete-potential-batch';live=read(batch/'data/batch-progress.json');assert live['status']=='RUNNING'
raw=subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-Process -Id {int(live["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName,StartTime | ConvertTo-Json -Compress'],text=True)
process=json.loads(raw);assert process['Id']==live['pid'] and process['ProcessName']=='python'
observed=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=live)
save('batch-observation.json',observed)
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
save('additional-batch-evidence.json',[p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
assert refs['HEAD']==refs['origin/main']
checkpoint=dict(status='PASS_LOCAL_COUNT_EXCLUSION_UNCHANGED_COMPARISONS',previous_goal_turn='progress',recorded_at=observed['recorded_at'],
    prior_checkpoint=prior_path.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior_path),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),batch_observation_sha256=sha(HERE/'data/batch-observation.json'),
    final_review_sha256=sha(HERE/'audit/final-review.md'),mathematical_note_sha256=sha(HERE/'mathematical-note.md'),
    checked_final_modules=65,theorem_axiom_audits=6,new_mathematical_definitions=0,
    remaining_reference_entries=1366,recovered_reference_indices=prior['recovered_reference_indices'],
    count_exclusion=dict(directions=[0,1,2,3,4,0],counts=[5,5,2,4,5],actual_snake_checked=True),
    additional_excluded_keys=865,total_excluded_keys=2957,restricted_graph_keys=4944051,
    hypothetical_seven_additional_exclusions=4773,complete_restricted_graph_lean_certificate=False,
    profile_comparisons=[dict(profile='completed',mean=483,range=551,integer=235),dict(profile='conditional',mean=496,range=602,integer=234)],
    maintained_interval=[191,235],upper_bound_evidence='Contributor proof and archived audit; full independent rebuild pending.',
    conditional_target=234,exact_optimum_unresolved=True,paper_revision=106,next_paper_revision=116,paper_sha256=sha(paper),
    git_refs_before_commit=refs,scope='One new actual-snake restriction; both numerical comparisons unchanged even assuming all seven candidates. Six further local exclusions, residual reference union, and complete graph certificates remain unresolved.')
save('checkpoint.json',checkpoint)
counts=live['contexts_checked_by_profile']
summary=f'''A new checked restriction excludes counts (5,5,2,4,5) on canonical
six-transition direction window 012340. Lean checks the local clause
semantics, contradiction, actual-snake statement, and both graph orientations.
Sixty-five modules pass, with six printed axiom reports. The proof has
1,664 input clauses, 2,007 deductions and 177,364 hints; independent RUP
replay also passes. No new mathematical definition was introduced.

The theorem removes 865 additional keys beyond milestone 109's 2,092,
leaving 4,944,051. It breaks the previously displayed completed-profile
cycle, but a different cycle keeps the mean 483 and range 551. The
conditional profile remains mean 496 and range 602. Assuming all seven
proposed exclusions removes 4,773 additional keys, with the same comparisons.
All seven native count probes reported UNSAT; edge 2139224 needed three
cycle cuts. Only edge 3534483 has a checked theorem in this round.

The scan of all 143 older proof roots found no relaxed candidate hitting
the original limiting cycles. Hypothetical share floors 76 on the seven
patterns also leave both comparisons unchanged. The next priority is a
restriction covering a family of surviving count patterns; test both full
profiles before investing in further isolated certificates.

At the saved process-verified observation, milestone 104 was RUNNING with
{counts['completed']}/791 completed and {counts['conditional']}/791 conditional contexts
checked; its active module was {live['active']['module']}. The running
batch and original graph were left intact. The reference union still has
1,366 unresolved entries, after the twelve checked in earlier milestones.

The maintained interval remains 191 through 235 edges, based on the
contributor proof and archived audit with its full independent rebuild
pending. Conditional 234 remains unresolved. The exact optimum and 196
remain open. Paper revision 106 is unchanged; the next full revision is 116.
'''
latest='Latest continuation: [milestone 110](milestones/110-critical-cycle-core-screen/README.md) proves a new local count exclusion for actual snakes and removes 865 additional graph keys. Both numerical comparisons remain unchanged, even assuming all seven proposed exclusions. The complete potential batch continues.'
priority='Next research priority: Seek one count inequality or interval exclusion covering a family of the surviving limiting-cycle patterns, and test its effect on both full profiles before certifying isolated cases. All 143 older cores miss the original limiting cycles; all seven new exclusions together preserve the numerical comparisons. Preserve the running milestone 104 batch.'
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;txt=path.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        txt,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,txt,count=1,flags=re.M);assert n==1
    path.write_text(txt,encoding='utf-8')
path=ROOT/'milestones/README.md';txt=path.read_text(encoding='utf-8');i=txt.index('- [Milestone 109:');assert '- [Milestone 110:' not in txt
path.write_text(txt[:i]+'- [Milestone 110: critical-cycle count exclusion](110-critical-cycle-core-screen/README.md). One new actual-snake theorem removes 865 additional keys. Even all seven candidate exclusions preserve both numerical comparisons.\n\n'+txt[i:],encoding='utf-8')
path=ROOT/'RESEARCH_LEDGER.md';txt=path.read_text(encoding='utf-8');assert '## Milestone 110:' not in txt
path.write_text(txt+'\n\n## Milestone 110: local count exclusion and replacement cycles\n\n'+summary+'\n'+priority+'\n',encoding='utf-8')
path=ROOT/'handoff/CURRENT_STATUS.md';txt=path.read_text(encoding='utf-8');i=txt.index('## Milestone 109 checkpoint')
path.write_text(txt[:i]+'## Milestone 110 checkpoint\n\n'+summary+'\nEarlier checkpoint sections below are historical snapshots.\n\n'+txt[i:],encoding='utf-8')
for name in ['README.md','NEXT_AGENT_PROMPT.md']:(ROOT/'handoff'/name).write_bytes((HERE/'handoff-templates'/name).read_bytes())
print(json.dumps(dict(status=checkpoint['status'],batch_counts=counts,additional_batch_files=len(set(extra))),indent=2))
