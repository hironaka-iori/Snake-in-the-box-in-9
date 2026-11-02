"""Freeze revision106 and a verified observation of the still-running graph batch."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
save=lambda name,data:(HERE/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists(),'Do not overwrite a frozen checkpoint.'
v=read(HERE/'data/verification.json');assert v['status']=='PASS_PAPER106_SOURCE_AND_MATHEMATICAL_DATA'
assert sha(ROOT/'paper/snake9_research.tex')==v['paper_sha256']
assert sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==v['paper_sha256']
prior_path=ROOT/'milestones/105-reference-proof-closure/data/checkpoint.json';prior=read(prior_path)
batch=ROOT/'milestones/104-complete-potential-batch';live=read(batch/'data/batch-progress.json')
assert live['status']=='RUNNING'
raw=subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-Process -Id {int(live["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName,StartTime | ConvertTo-Json -Compress'],text=True)
process=json.loads(raw);assert process['Id']==live['pid'] and process['ProcessName']=='python'
snapshot=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=live)
save('batch-observation.json',snapshot)
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','--','milestones/104-complete-potential-batch'],cwd=ROOT,text=True).splitlines())
extra=[];contexts={'completed':set(),'conditional':set()}
for group in live['selected']:
    name=group['module'];rp=batch/'data'/(name+'-audit.json');r=read(rp)
    assert sha(rp)==group['receipt_sha256'] and r['status']=='PASS_COMPLETE_BATCH_MODULE'
    assert r['exit_code']==0
    assert sha(batch/'lean'/(name+'.lean'))==r['source_sha256']==sha(batch/r['source_snapshot'])
    assert sha(batch/r['log'])==r['log_sha256']
    assert sha(batch/'build'/(name+'.olean'))==r['olean_sha256']
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for ctx in group['contexts']:
        key=tuple(ctx);assert key not in contexts[group['profile']];contexts[group['profile']].add(key)
    for p in [rp,batch/r['log'],batch/r['source_snapshot'],(batch/r['source_snapshot']).parent/'checker.py.txt']:
        if p.relative_to(ROOT).as_posix() not in tracked:extra.append(p)
for profile,ctxs in contexts.items():assert 6+len(ctxs)==live['contexts_checked_by_profile'][profile]
save('additional-batch-evidence.json',[p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
assert refs['HEAD']==refs['origin/main']
assert (HERE/'audit/independent-review.md').exists()
compile_info=read(HERE/'data/compile-diagnostic.json')
c=dict(status='PASS_PAPER106_SOURCE_WITH_COMPILER_UNAVAILABLE',previous_goal_turn='progress',
    recorded_at=snapshot['recorded_at'],prior_checkpoint=prior_path.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior_path),
    verification_sha256=sha(HERE/'data/verification.json'),revision_sha256=sha(HERE/'data/revision.json'),
    independent_review_sha256=sha(HERE/'audit/independent-review.md'),compile_diagnostic_sha256=sha(HERE/'data/compile-diagnostic.json'),
    batch_observation_sha256=sha(HERE/'data/batch-observation.json'),paper_sha256=v['paper_sha256'],
    paper_revision=106,next_scheduled_paper_revision=116,new_definitions=0,named_definitions=1,
    new_lean_checks=0,printed_snakes=13,vertex_pair_checks=118673,
    unconditional_edge_interval=[191,235],conditional_target=234,upper_bound_evidence=prior['upper_bound_evidence'],
    pending_reference_proposition=prior['pending_reference_proposition'],reference_union_refutation_checked=False,
    complete_graph_potential_certificates_checked=False,pending_conditional_local_cases=prior['pending_conditional_local_cases'],
    pending_share_floors=prior['pending_share_floors'],case7302_state=prior['case7302_state'],
    compiler_status=compile_info['status'],git_refs_before_commit=refs,
    scope='Manuscript update through105, source preservation and arithmetic/receipt checks; no new Lean proof or numerical bound. Complete potential batch continues; PDF compilation failed before TeX.')
save('checkpoint.json',c)
counts=live['contexts_checked_by_profile']
summary=f'''The manuscript now presents the checked graph coverage, complete actual
weight interpretation and exact 1,378-key reference-union implication. Its
conditional 234 route uses pending floors (16,18,16,16,16), slope496 and range602.
The earlier floor20/range600 optimality result is kept separate. No smaller
unconditional numerical bound is claimed.

Named definitions were reduced from three to one, with no new definitions.
The source preserves all authors, hyperlink settings, appendices and printed
witnesses. All13 snakes pass118,673 pair checks. There are135 statement blocks:
130 prior blocks are unchanged, two propositions are strengthened using checked
results, two definition environments become prose, and three deductions are
added from existing evidence. This milestone ran no new Lean compiler.

The built-in compiler failed before processing TeX because its Windows helper
could not enforce the required writable roots. No current PDF or visual layout
is verified. The exact diagnostic is saved.

At the saved process-verified observation, milestone104 was RUNNING with
{counts['completed']}/791 completed-profile contexts and {counts['conditional']}/791
conditional-profile contexts checked. The recorded active module was
{live['active']['module']}. This is a dated snapshot, not a live total.

The maintained interval remains191 through235 edges. The contributor235 proof
retains its inspected source and archived audit; a complete independent rebuild
is pending. The reference refutations, full potential certificates and five
conditional share bounds remain separate obligations. The exact optimum and
conjecture196 remain unresolved.
'''
# Keep ordinary spacing in all shared documents.
summary=re.sub(r'(?<=[A-Za-z])(\d)',r' \1',summary)
summary=re.sub(r'(\d)(?=[A-Za-z])',r'\1 ',summary)
priority=('Next research priority: Preserve and complete the active milestone 104 graph certificate batch, then audit both final assemblies. Recover the exact reference refutation roots selected in milestone 105. Conditional 234 still needs the five local shares, with a separate target-18 proof for 012034. The next scheduled full paper revision is 116.')
latest=('Latest continuation: [milestone 106](milestones/106-paper-revision/README.md) revises the manuscript through milestone 105, reduces named definitions from three to one, and states the exact remaining assumptions. Source and witness checks pass; built-in PDF compilation is unavailable. The complete potential batch remains active and the numerical interval is unchanged.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t,encoding='utf-8')
p=ROOT/'milestones/README.md';t=p.read_text(encoding='utf-8');i=t.index('- [Milestone 105:')
assert '- [Milestone 106:' not in t
p.write_text(t[:i]+'- [Milestone 106: manuscript revision and precise remaining assumptions](106-paper-revision/README.md). Fewer named definitions; checked graph and weight chain; conditional floor 18; PDF compiler unavailable.\n\n'+t[i:],encoding='utf-8')
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text(encoding='utf-8');assert '## Milestone 106:' not in t
p.write_text(t+'\n\n## Milestone 106: manuscript revision\n\n'+summary+'\n'+priority+'\n',encoding='utf-8')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text(encoding='utf-8');i=t.index('## Milestone 105 checkpoint')
p.write_text(t[:i]+'## Milestone 106 checkpoint\n\n'+summary+'\nEarlier sections below retain their historical snapshots. The exact union is\nthe current reference premise, and paper revision 106 supersedes revision 96.\n\n'+t[i:],encoding='utf-8')
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md) and the
[continuation assignment](NEXT_AGENT_PROMPT.md). The latest saved round is
[milestone 106](../milestones/106-paper-revision/README.md), a manuscript revision.
The checked mathematical chain is in milestones 97, 98, 99 and 105.

Milestone 104's complete potential batch remains active. Read its live record
and verify the recorded process before any action. Do not start another copy
or edit its live sources, checker or generator.

The current bound chain needs refutations for the exact 1,378-key union and
the complete graph certificates. Conditional 234 additionally needs the five
local floors (16,18,16,16,16). Coverage, weight interpretation, the total
charge budget, potential ranges and conditional telescoping are checked.

The maintained interval is 191 through 235 edges; the contributor's upper
bound retains its archived audit and pending independent rebuild. The exact
optimum is unresolved. The original case 7302 target-20 replay remains stopped.

Paper revision 106 preserves Iori Hironaka, Tommy Ma and Steven Zhan as authors
and the existing hyperlink settings. The open D: source and E: repository
mirror are identical. The built-in compiler failed before TeX processing;
no new PDF is verified. Only necessary, repeatedly used definitions should
be introduced. The next full manuscript revision is scheduled for 116.
''',encoding='utf-8')
prompt=(ROOT/'handoff/NEXT_AGENT_PROMPT.md').read_text(encoding='utf-8')
prompt=prompt.replace('Read milestone 105\'s\nmathematical note and checkpoint, then the live record and NEXT.md in',
    'Read milestone 106\'s checkpoint and revision audit, milestone 105\'s\nmathematical note, then the live record and NEXT.md in')
a=prompt.index('## Scheduled manuscript revision and runtime');b=prompt.index('Python is ',a)
prompt=prompt[:a]+'''## Manuscript and runtime

Revision 106 is complete at source level. Its verification preserves all
appendices, authors and hypersetup settings and checks all 13 printed snakes.
The built-in compiler failed before TeX processing because of the Windows
helper's writable-root restriction; no successful PDF or visual review is
claimed. The exact sources are synchronized between
D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and
E:/Snake-in-a-box/paper/snake9_research.tex. Continue editing the open source
in place. The next full paper revision is scheduled for 116.

Use ordinary mathematical notation. Introduce a definition only if necessary
and repeatedly used. Keep Lean filenames and implementation definitions out
of the manuscript. The current argument distinguishes old floor20/range600
optimality from the sufficient floor18/range602 profile.

'''+prompt[b:]
(ROOT/'handoff/NEXT_AGENT_PROMPT.md').write_text(prompt,encoding='utf-8')
p=ROOT/'paper/README.md';t=p.read_text(encoding='utf-8');i=t.index('Current logical revision:')
p.write_text(t[:i]+'''Current logical revision: milestone 106. The maintained interval is
$191\\le a(9)\\le235$ edges; 234 remains conditional. The paper presents complete
graph coverage and weight interpretation, the exact reference-union premise,
and the reduced pending floors (16,18,16,16,16). The old floor20/range600
comparison is distinguished from the current floor18/range602 certificate.

There are 135 statement blocks and 204 resolved labels. All appendices and
13 printed snakes are preserved; 118,673 pairwise adjacency checks pass.
130 prior statement blocks are unchanged. Two propositions have strengthened
checked conclusions, two definition environments become ordinary prose, and
three statements consolidate existing results. Named definitions decrease
from three to one; none is added. Editor and repository sources are identical.

The built-in preview failed before TeX processing because the Windows compiler
helper could not start with the required writable roots. A new PDF and page
layout have not been verified. Existing PDFs are not revision106 outputs.
See [revision 106](../milestones/106-paper-revision/README.md) for exact checks
and the compiler diagnostic.
''',encoding='utf-8')
(HERE/'README.md').write_text('''# Milestone 106: manuscript revision

The open manuscript and repository mirror now incorporate the checked
arguments through milestone 105. Only one named definition remains, for
the problem itself. Existing endpoint and cycle notation is stated in prose.
No mathematical definition was added.

The paper presents the exact 1,378-key reference premise, complete graph
coverage, full weight interpretation, total charge and conditional upper-bound
assembly. It reduces the required 012034 share from 20 to 18 and distinguishes
the resulting range-602 certificate from the earlier range-600 optimum.

The maintained interval remains 191 through 235 edges. The conditional target
234 still needs the reference refutations, complete potential certificate and
five local share claims. This editorial round proves no new numerical bound
and ran no new Lean checks.

Read the [verification](data/verification.json), [independent review](audit/independent-review.md),
[checkpoint](data/checkpoint.json), and [continuation assignment](../../handoff/NEXT_AGENT_PROMPT.md).
The full original source is preserved in data/paper-before.zip. All appendices,
authors and hyperlink settings are unchanged. All 13 printed snakes pass
118,673 pair checks. Existing checked proof receipts are re-audited.

The built-in compiler failed before TeX processing because of its Windows
execution environment. The [diagnostic](data/compile-diagnostic.json) is saved;
no current PDF or visual layout is verified. The active milestone 104 batch
is untouched; this round records and verifies an immutable progress snapshot.
The next scheduled full manuscript revision is 116.
''',encoding='utf-8')
print(json.dumps(dict(status=c['status'],paper_revision=106,batch_counts=counts,extra_batch_files=len(set(extra))),indent=2))
