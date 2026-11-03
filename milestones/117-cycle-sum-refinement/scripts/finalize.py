"""Freeze the research round and process-verified continuation state."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
save=lambda name,data:(HERE/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists()
verification=read(HERE/'data/verification.json');assert verification['status']=='PASS_EXACT117_EVIDENCE'
assert (HERE/'audit/final-review.md').exists()
receipt=read(HERE/'data/SumGeometry117-audit.json')
save('proof-summary.json',dict(status='PASS_CONDITIONAL_GEOMETRY_ARITHMETIC_AND_NATIVE_REFINEMENT',
    modules=[dict(module='SumGeometry117',receipt_sha256=sha(HERE/'data/SumGeometry117-audit.json'),theorem_audits=receipt['theorem_audits'])],
    native_original_certificate_sha256=sha(HERE/'data/012034-middle5-outer15-certificate.json'),
    selected_native_replay_sha256=sha(HERE/'data/replay-core0.json'),successful_modules=1,axiom_reports=3,
    actual_local_theorem_checked=False,concrete_sum_semantics_checked=False,complete_lean_contradiction_checked=False,new_definitions=0,
    scope='Conditional actual-snake transfer and arithmetic pass Lean. Native contradiction independently replayed; full Lean chain pending.'))
batches=[]
for folder in ['104-complete-potential-batch','115-total-count-certificate']:
    state=read(ROOT/'milestones'/folder/'data/batch-progress.json');pid=int(state['pid'])
    raw=subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-CimInstance Win32_Process -Filter "ProcessId = {pid}" | Select-Object ProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Compress'],text=True,encoding='utf-8')
    process=json.loads(raw)
    assert state['status']=='RUNNING' and process['ProcessId']==pid and folder in process['CommandLine']
    save(folder[:3]+'-batch-observation.json',dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=state))
    batches.append(dict(milestone=int(folder[:3]),pid=pid,status=state['status'],active=state.get('active'),
        contexts=state.get('contexts_checked_by_profile'),checked_modules=len(state.get('checked_modules',[])),
        observation_sha256=sha(HERE/'data'/(folder[:3]+'-batch-observation.json'))))
prior=ROOT/'milestones/116-paper-revision/data/checkpoint.json'
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
checkpoint=dict(status='PASS_NATIVE_COUNT_REFINEMENT_WITH_CONDITIONAL_LEAN_TRANSFER',previous_goal_turn='progress',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),prior_checkpoint=prior.relative_to(ROOT).as_posix(),
    prior_checkpoint_sha256=sha(prior),verification_sha256=sha(HERE/'data/verification.json'),proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    final_review_sha256=sha(HERE/'audit/final-review.md'),graph_review_sha256=sha(HERE/'audit/graph-review.md'),graph_audit_sha256=sha(HERE/'data/graph-audit.json'),
    archive_manifest_sha256=sha(HERE/'data/large-artifact-archives.json'),maintained_edge_interval=[191,235],conditional_target=234,remaining_reference_entries=1366,
    new_definitions=0,successful_lean_modules=1,axiom_reports=3,local_count_theorem_checked=False,
    complete_graph_potential_certificates_checked=False,upper_bound_independent_rebuild_complete=False,
    completed_profile_mean='2915/6',completed_profile_range='1730/3',conditional_profile_mean=496,conditional_profile_range=602,
    paper_revision=116,next_scheduled_paper_revision=126,paper_sha256=verification['paper_sha256'],live_batches=batches,git_refs_before_commit=refs,
    scope='Replayed native count contradiction, checked conditional transfer and arithmetic, improved conditional finite comparison. No new global bound.')
save('checkpoint.json',checkpoint)
counts=batches[0]['contexts'];count115=batches[1]['checked_modules']
body=f'''The new candidate on 012034 states that a middle count at most 5 forces
the outer four counts to sum to at least 16. Both previous attaining cycles
violate it. A complete native contradiction passes independent replay.
The reduced proof has 142,180 deductions and 8,712,029 hints, using 1,709
variables. Its 5,114 used clauses map exactly into the original formula.
The earlier proof is preserved. Concrete sum semantics and the full Lean
contradiction remain pending.

Lean checks the actual-snake transfer with that local contradiction as an
explicit hypothesis, plus two comparison deductions. One module and three
standard axiom reports pass. No mathematical definition was added. The first
attempt launched no compiler because the memory gate was closed; the waited
retry passed. Both attempt records remain saved.

The new rule removes 23,285 further graph edges. The completed-floor mean
increases from 6309/13 to 2915/6, with range 1730/3 and comparison 1324108/5623.
The conditional-floor mean/range remains 496/602. Integer comparisons remain
235 and 234. Both experiments assume unproved local rules. Independent
saved-cycle and potential audits pass; the producer supplies the all-edge
lower certificates.

All applicable deficits vanish on the replacement 18-edge and 3-edge cycles.
Changing coefficients within this eleven-rule family cannot improve their
mean ceilings. Range reduction alone also cannot improve the integer bounds.
The next shared target is 012301, with exact outer sums 11 and 12 and middle
count in [6,21]. An outer lower bound 13 remains an untested candidate.

The independently checked local witness (5,3,5,3,6) has outer sum 17 and five
components. It is not a complete snake. Outer sum at most 16, unrestricted
total at most 20, and total at most 20 with all counts at most 5 remain UNKNOWN
in bounded runs. The candidate lower bound 16 is not shown sharp.

At this process-verified snapshot, milestone 104 reports
{counts['completed']}/791 completed-profile and {counts['conditional']}/791 conditional-profile contexts;
milestone 115 reports {count115}/1397 checked modules. Both drivers are live.
Their final certificates and the 012310 actual theorem remain pending.
Neither batch was restarted or changed.

The maintained interval remains 191 through 235 edges, with the contributor
proof and archived audit for 235 and its complete independent rebuild pending.
Conditional 234, the optimum and 196 remain unresolved. There are 1,366
outstanding reference entries. Paper revision 116 is unchanged; next revision 126.
'''
priority='Next research priority: Preserve both live proof batches. Check existing witnesses, then test outer sum at most 12 on canonical 012301; replacement cycles have outer sums 11 and 12 with middle count in [6,21]. Compare any viable restriction on both profiles. The 012034 outer-16 candidate still needs concrete Lean semantics and full contradiction. Next paper revision: 126.'
latest='Latest continuation: [milestone 117](milestones/117-cycle-sum-refinement/README.md) replays a count-sum contradiction that removes both prior attaining cycles. The conditional finite mean rises to 2915/6; integer comparisons remain 235 and 234. Lean checks the conditional geometric transfer and arithmetic. No new definitions or global bound.'
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;text=path.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        text,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,text,count=1,flags=re.M);assert n==1
    path.write_text(text,encoding='utf-8')
path=ROOT/'milestones/README.md';text=path.read_text(encoding='utf-8');i=text.index('- [Milestone 116:')
assert '- [Milestone 117:' not in text
path.write_text(text[:i]+'- [Milestone 117: count-sum refinement on both surviving cycles](117-cycle-sum-refinement/README.md). Replayed native contradiction; conditional Lean transfer; finite mean 2915/6; integer comparisons unchanged.\n\n'+text[i:],encoding='utf-8')
path=ROOT/'RESEARCH_LEDGER.md';text=path.read_text(encoding='utf-8');assert '## Milestone 117:' not in text
path.write_text(text+'\n\n## Milestone 117: a count-sum refinement\n\n'+body+'\n'+priority+'\n',encoding='utf-8')
path=ROOT/'handoff/CURRENT_STATUS.md';text=path.read_text(encoding='utf-8');i=text.index('## Milestone 116 checkpoint')
path.write_text(text[:i]+'## Milestone 117 checkpoint\n\n'+body+'\nEarlier checkpoints below are historical snapshots.\n\n'+text[i:],encoding='utf-8')
(ROOT/'handoff/README.md').write_text('# Research handover\n\nRead [current status](CURRENT_STATUS.md), [next steps](NEXT_AGENT_PROMPT.md),\nand [milestone 117](../milestones/117-cycle-sum-refinement/README.md).\n\n'+body,encoding='utf-8')
path=ROOT/'handoff/NEXT_AGENT_PROMPT.md';text=path.read_text(encoding='utf-8')
path.write_text('''# Continuation after milestone 117

Work in E:/Snake-in-a-box. Read the latest mathematical note and checkpoint.
Use the research skill with formal, concise prose. Introduce definitions
only when essential and repeatedly used. Keep the existing count notation
and the empty-square/count-sum route.

'''+priority+'''

The selected native proof is work/core0/core.trim.lrat in milestone 117.
Its input identifiers are in data/refine-core0.json; independent original-CNF
replay is in data/replay-core0.json. Preserve the 84 repeated counter entries.
An active-variable bijection is needed before bounded-literal export;
the selected proof uses 1,709 variables. No full Lean contradiction or actual
local theorem is claimed. The conditional transfer passes Lean.

Use scripts/verify_saved.py --restore-archives after a clone to restore
missing large proofs without overwriting differing bytes. Inspect saved
attempts and live processes before retrying work. Do not duplicate either
active batch or edit its pinned inputs. Paper and editor remain revision 116;
revise next at 126. Preserve authors and hypersetup, unrelated local changes,
and exact audited bytes. Stage only the reviewed milestone manifest. The
full research goal remains active.

## Earlier continuation record

'''+text,encoding='utf-8')
(HERE/'README.md').write_text('''# Milestone 117: a count-sum restriction on the surviving cycles

Read the [mathematical note](mathematical-note.md), [graph review](audit/graph-review.md),
[final review](audit/final-review.md), [proof summary](data/proof-summary.json),
and [checkpoint](data/checkpoint.json).

'''+body+'''
## Reproduction and continuation

- `data/probes/` retains all five outcomes, including unresolved runs.
- `work/012034-middle5-outer15/` retains the original formula and first proof.
- `work/core0/` retains the selected proof; see `data/replay-core0.json`.
- `lean/SumGeometry117.lean` and its receipt check the conditional geometric
  implication and comparison arithmetic. The contradiction remains a premise.
- `data/middle5-outer16/` contains both finite comparisons and potentials.
- `archives/` contains verified gzip copies of the four large native proofs;
  all originals remain local.
- `scripts/verify_saved.py --verify` checks the frozen package;
  `--restore-archives` restores missing proofs without overwriting different data.

Both compiler attempts are retained; see `audit/attempts.md`. The paper is unchanged.
''',encoding='utf-8')
print(json.dumps({k:v for k,v in checkpoint.items() if k!='live_batches'},indent=2))
