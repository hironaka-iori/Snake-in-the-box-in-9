"""Freeze the relaxed exclusion and save a process-verified batch observation."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
save=lambda name,data:(HERE/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists() and not (HERE/'data/check.lock').exists()
proof=read(HERE/'data/proof-summary.json')
assert proof['status']=='PASS_ACTUAL_SNAKE_EXCLUSION_AND_RESTRICTED_GRAPH_AUDIT'
assert (HERE/'audit/final-review.md').exists()
prior_path=ROOT/'milestones/108-smaller-reference-recovery/data/checkpoint.json';prior=read(prior_path)
assert sha(ROOT/'paper/snake9_research.tex')==prior['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
batch=ROOT/'milestones/104-complete-potential-batch';live=read(batch/'data/batch-progress.json')
assert live['status']=='RUNNING'
raw=subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-Process -Id {int(live["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName,StartTime | ConvertTo-Json -Compress'],text=True)
process=json.loads(raw);assert process['Id']==live['pid'] and process['ProcessName']=='python'
snapshot=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=live)
save('batch-observation.json',snapshot)
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','--','milestones/104-complete-potential-batch'],cwd=ROOT,text=True).splitlines())
extra=[]
for group in live['selected']:
    name=group['module'];rp=batch/'data'/(name+'-audit.json');r=read(rp)
    assert sha(rp)==group['receipt_sha256'] and r['status']=='PASS_COMPLETE_BATCH_MODULE' and r['exit_code']==0
    assert sha(batch/'lean'/(name+'.lean'))==r['source_sha256']==sha(batch/r['source_snapshot'])
    assert sha(batch/r['log'])==r['log_sha256'] and sha(batch/'build'/(name+'.olean'))==r['olean_sha256']
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for p in [rp,batch/r['log'],batch/r['source_snapshot'],(batch/r['source_snapshot']).parent/'checker.py.txt']:
        if p.relative_to(ROOT).as_posix() not in tracked:extra.append(p)
save('additional-batch-evidence.json',[p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
assert refs['HEAD']==refs['origin/main']
c=dict(prior)
c.update(status='PASS_NEW_RESTRICTION_AND_UNCHANGED_PROFILE_BOUNDS',previous_goal_turn='progress',recorded_at=snapshot['recorded_at'],
    prior_checkpoint=prior_path.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior_path),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),batch_observation_sha256=sha(HERE/'data/batch-observation.json'),
    final_review_sha256=sha(HERE/'audit/final-review.md'),mathematical_note_sha256=sha(HERE/'mathematical-note.md'),
    checked_final_modules=10,theorem_axiom_audits=16,new_mathematical_definitions=0,
    recovered_reference_indices=proof['recovered_reference_indices'],relaxed_bounds=proof['relaxed_bounds'],pending_reference_entries=1366,
    remaining_union_equivalence='Snake9.RelaxedGraph109.reference_union_iff_remaining_twelve',
    pending_reference_proposition='AllRefutedList of referenceKeys filtered to omit the twelve explicit keys in ReferenceCoverage109',
    excluded_full_keys=2092,restricted_graph_edges=4944916,actual_snake_restriction_checked=True,
    complete_restricted_graph_lean_certificate=False,comparison_range_barriers_checked=True,
    restricted_profiles_sha256=sha(HERE/'data/restricted-profiles.json'),obstruction_survival_sha256=sha(HERE/'data/obstruction-survival.json'),
    git_refs_before_commit=refs,
    scope='A checked actual-snake restriction excludes 2092 graph keys. Both profile means/ranges and all five floor obstructions survive. Range reduction alone cannot improve the integer bounds while those means survive. Twelve reference entries are checked,1366 remain. No new numerical bound.')
save('checkpoint.json',c)
counts=live['contexts_checked_by_profile']
summary=f'''For five consecutive distinct transition directions, a new checked
restriction requires the first singleton-square count to be at least 2,
the second to be at least 6, or the fourth to be at least 3. The third is
unrestricted. The 441-clause core has 270 regenerated deductions and 1,343
hints. Lean checks the relaxed semantics and its actual-snake application.

Exact enumeration excludes 2,092 of 4,947,008 accepted full graph keys.
The separate restricted experiment has 4,944,916 keys. Both sharp cycles
survive: the profiles remain at mean 483/range 551 and mean 496/range 602.
All five one-unit floor obstructions survive. All sixteen screened relaxed
boxes miss both sharp cycles. Lean also checks that even range zero cannot
improve either integer comparison while the respective mean survives.

Twelve exact reference entries are now checked. Lean proves the full union
equivalent to the filtered assertion for 1,366 remaining entries. Ten final
modules and sixteen printed axiom reports pass. No mathematical definition
was added. The native graph computations remain separately labelled evidence.

At the immutable process-verified observation, milestone 104 was RUNNING with
{counts['completed']}/791 completed-profile contexts and {counts['conditional']}/791
conditional-profile contexts checked. Its active module was {live['active']['module']}.
The active original graph, checker and generator remain unchanged.

The maintained interval remains 191 through 235 edges. The contributor proof
and archived audit support 235, with a complete independent rebuild pending.
Conditional 234 still needs the remaining reference union, complete graph
certificates and five local floors (16,18,16,16,16). The exact optimum and
conjecture 196 remain open. Paper revision 106 is unchanged; next revision 116.
'''
latest='Latest continuation: [milestone 109](milestones/109-relaxed-graph-test/README.md) proves a restriction for actual snakes and excludes 2,092 graph keys in a separate experiment. Both numerical profile bounds remain unchanged. Twelve reference entries are checked and 1,366 remain; the complete potential batch continues.'
priority='Next research priority: Screen the remaining archived cores for relaxed count bounds that exclude a current sharp-cycle key. All sixteen small candidates screened in milestone 109 miss both sharp cycles. Rank cycle hits before removed-edge counts and verify candidate restrictions in Lean. Preserve the running milestone 104 batch.'
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t,encoding='utf-8')
p=ROOT/'milestones/README.md';t=p.read_text(encoding='utf-8');i=t.index('- [Milestone 108:');assert '- [Milestone 109:' not in t
p.write_text(t[:i]+'- [Milestone 109: actual-snake restriction and graph test](109-relaxed-graph-test/README.md). A checked restriction excludes 2,092 keys; both profile bounds and five floor obstructions survive. Twelve reference entries checked, 1,366 remaining.\n\n'+t[i:],encoding='utf-8')
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text(encoding='utf-8');assert '## Milestone 109:' not in t
p.write_text(t+'\n\n## Milestone 109: new restriction and unchanged profile bounds\n\n'+summary+'\n'+priority+'\n',encoding='utf-8')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text(encoding='utf-8');i=t.index('## Milestone 108 checkpoint')
p.write_text(t[:i]+'## Milestone 109 checkpoint\n\n'+summary+'\nEarlier checkpoint sections below are historical snapshots.\n\n'+t[i:],encoding='utf-8')
for name in ['README.md','NEXT_AGENT_PROMPT.md']:
    (ROOT/'handoff'/name).write_bytes((HERE/'handoff-templates'/name).read_bytes())
print(json.dumps(dict(status=c['status'],remaining_reference_entries=1366,batch_counts=counts,additional_batch_files=len(set(extra))),indent=2))
