"""Publish the reviewed round to the local handover and freeze a live-batch observation."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,data):
    p=HERE/'data'/name;assert not p.exists();p.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists()
proof=read(HERE/'data/proof-summary.json')
assert proof['status']=='PASS_NATIVE_TOTAL_CERTIFICATE_CONDITIONAL_TRANSFER_AND_GRAPH_COMPARISONS'
assert len(proof['modules'])==2 and len(proof['theorem_audits'])==4
for p,digest in proof['source_files_sha256'].items():assert sha(ROOT/p)==digest,p
assert (HERE/'audit/final-review.md').exists()
prior_path=ROOT/'milestones/113-all-four-sum-pressure/data/checkpoint.json';prior=read(prior_path)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==prior['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
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
for rel in ['logs/ConditionalBatch104G080-1793661117967943200-record.json',
            'logs/ConditionalBatch104G080-1793661117967943200.log','logs/check-run-1793661117967943200.json',
            'logs/attempt-1793661117967943200/ConditionalBatch104G080.lean.txt',
            'logs/attempt-1793661117967943200/checker.py.txt','logs/batch-1793649486435169100.log']:
    p=batch/rel;assert p.exists()
    if p.relative_to(ROOT).as_posix() not in tracked:extra.append(p)
for stream in ['stdout','stderr']:
    source=HERE/'logs'/('resumed-batch.'+stream+'.log')
    target=HERE/'logs'/('resumed-batch-'+stream+'-snapshot.txt');assert not target.exists()
    target.write_bytes(source.read_bytes())
refs={r:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',r],cwd=ROOT,text=True).strip()
      for r in ['HEAD','origin/main','origin/research/unconditional-241']}
assert refs['HEAD']==refs['origin/main']
counts=live['contexts_checked_by_profile']
summary=f'''The native contradiction for five-count total at most 18 on canonical
012310 has been independently replayed in both core and original-CNF
identifier systems. It uses 5,206 input clauses, 358,464 deductions and
22,088,504 propagation hints. Its concrete counter interpretation and
full Lean replay remain pending. Lean checks the conditional geometric
transfer and three exact comparison lemmas: two modules, four standard
axiom reports, and no new mathematical definitions.

The nine-rule finite experiment removes 2,263 further keys beyond 113,
retaining 4,865,603. Its completed-floor mean rises to 2424/5 with range 2881/5;
comparison 5517073/23424 retains integer 235. The conditional profile remains
496/602 and integer 234. A stronger total-20 hypothesis has an UNKNOWN
local probe, lowers only the first range to 565, and retains both integers.
Zero-deficit cycles fix coefficient ceilings 2424/5 and 496 in these families.
Both profiles continue to assume other unproved local rules.

The selected proof completed in 20.656 seconds using temporary storage,
after the same formula/options timed out at 60 seconds on the research
volume. Their first 40,935,424 proof bytes agree. Reusing 115 valid cycle
cuts produced a larger retained proof and was not selected. Preserve all
attempts and the independently replayed original certificate.

The next priority is reducing that certificate before concrete Lean
export. The subsequent common local target is 012345, with exact tuples
(4,3,3,5,4), (5,4,2,5,5), and (5,4,3,4,5). A middle count at most 3
and total at most 21 remains an untested combination.

Milestone 104 resumed after its unchanged interrupted module passed on
retry. This process-verified snapshot records {counts['completed']}/791 completed
and {counts['conditional']}/791 conditional contexts, with active module
`{live['active']['module']}`. Preserve the running batch. The reference
union still has 1,366 unresolved entries. No new global upper bound is
established; the maintained interval is 191 through 235 edges with the
full independent rebuild pending. Conditional 234 and the optimum remain
unresolved. Paper revision 106 is unchanged; next full revision 116.
'''
latest='Latest continuation: [milestone 114](milestones/114-total-count-pressure/README.md) independently replays a native total-count contradiction and checks its conditional geometric transfer. The completed-floor finite mean improves to 484.8; integer comparisons remain 235 and conditional 234. Concrete Lean replay is the next proof obligation.'
priority='Next research priority: Reduce the selected 012310 total-count certificate and export its concrete semantics and refutation to Lean. Preserve the resumed milestone 104 batch. Subsequently test the recorded 012345 count cells on both profiles; avoid coefficient sweeps within the current fixed families.'
updates={}
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;txt=p.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        txt,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,txt,count=1,flags=re.M);assert n==1
    updates[p]=txt
p=ROOT/'milestones/README.md';txt=p.read_text(encoding='utf-8');i=txt.index('- [Milestone 113:');assert '- [Milestone 114:' not in txt
updates[p]=txt[:i]+'- [Milestone 114: total-count pressure and native proof replay](114-total-count-pressure/README.md). Independently replayed contradiction, checked conditional geometry and comparison arithmetic; finite mean improves to 484.8, with integer comparisons unchanged.\n\n'+txt[i:]
p=ROOT/'RESEARCH_LEDGER.md';txt=p.read_text(encoding='utf-8');assert '## Milestone 114:' not in txt
updates[p]=txt+'\n\n## Milestone 114: total-count certificate and finite comparisons\n\n'+summary+'\n'+priority+'\n'
p=ROOT/'handoff/CURRENT_STATUS.md';txt=p.read_text(encoding='utf-8');i=txt.index('## Milestone 113 checkpoint');assert '## Milestone 114 checkpoint' not in txt
updates[p]=txt[:i]+'## Milestone 114 checkpoint\n\n'+summary+'\nEarlier checkpoint sections below are historical snapshots.\n\n'+txt[i:]
checkpoint=dict(status='PASS_NATIVE_TOTAL_CERTIFICATE_AND_CONDITIONAL_GRAPH_IMPROVEMENT',previous_goal_turn='progress',recorded_at=observed['recorded_at'],
    prior_checkpoint=prior_path.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior_path),
    checked_final_modules=2,theorem_axiom_audits=4,new_mathematical_definitions=0,
    native_contradiction_replayed=True,concrete_lean_contradiction_checked=False,geometric_transfer_has_local_premise=True,
    selected_core_clauses=5206,selected_lemmas=358464,selected_hints=22088504,
    conditional_graph_keys=4865603,hypothetical_stronger_graph_keys=4859836,
    family_profile_comparisons=[dict(profile='completed',mean='2424/5',range='2881/5',comparison='5517073/23424',integer=235),
        dict(profile='conditional',mean='496',range='602',comparison='551765/2348',integer=234)],
    total20_local_probe='UNKNOWN',fixed_family_coefficient_ceilings=['2424/5','496'],remaining_reference_entries=1366,
    recovered_reference_indices=prior['recovered_reference_indices'],maintained_interval=[191,235],conditional_target=234,
    exact_optimum_unresolved=True,new_global_bound=False,
    upper_bound_evidence='Contributor proof and archived audit; complete independent rebuild pending.',
    next_priority='Reduce selected native proof and check concrete semantics/refutation in Lean; then test the recorded012345 cells.',
    paper_revision=106,next_paper_revision=116,paper_sha256=sha(paper),git_refs_before_commit=refs,
    evidence_sha256={p:sha(HERE/p) for p in ['data/proof-summary.json','data/012310-total18-certificate.json','data/cycle-audit.json',
        'audit/final-review.md','mathematical-note.md','data/total19/results.json','data/total20-hypothesis/results.json',
        'data/large-artifact-archives.json','data/pooled-trim.json']},
    scope='Native contradiction independently replayed; concrete Lean proof remains pending. Two checked helper modules and conditional finite mean improvement, with unchanged integer comparisons and no new global bound.')
save('batch-observation.json',observed);checkpoint['batch_observation_sha256']=sha(HERE/'data/batch-observation.json')
save('additional-batch-evidence.json',[p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
for p,txt in updates.items():p.write_text(txt,encoding='utf-8')
for name in ['README.md','NEXT_AGENT_PROMPT.md']:(ROOT/'handoff'/name).write_bytes((HERE/'handoff-templates'/name).read_bytes())
save('checkpoint.json',checkpoint)
print(json.dumps(dict(status=checkpoint['status'],batch_counts=counts,additional_batch_files=len(set(extra))),indent=2))
