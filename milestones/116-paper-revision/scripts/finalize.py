"""Freeze the revised paper and read-only observations of the ongoing batches."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,zipfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
save=lambda name,data:(HERE/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists(),'Do not overwrite a frozen checkpoint.'
v=read(HERE/'data/verification.json');assert v['status']=='PASS_PAPER116_SOURCE_AND_MATHEMATICAL_DATA'
assert sha(ROOT/'paper/snake9_research.tex')==v['paper_sha256']
assert sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==v['paper_sha256']
assert (HERE/'audit/independent-review.md').exists()
prior=ROOT/'milestones/115-total-count-certificate/data/checkpoint.json'
snapshots=[];evidence={};receipt_count=0
for folder in ['104-complete-potential-batch','115-total-count-certificate']:
    base=ROOT/'milestones'/folder;state=read(base/'data/batch-progress.json')
    assert state['status']=='RUNNING'
    pid=int(state['pid'])
    proc=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-CimInstance Win32_Process -Filter "ProcessId = {pid}" | Select-Object ProcessId,Name,CreationDate,CommandLine | ConvertTo-Json -Compress'],text=True,encoding='utf-8'))
    assert proc['ProcessId']==pid and 'python' in proc['Name'].lower() and folder in proc['CommandLine']
    observation=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=proc,state=state)
    save(folder[:3]+'-batch-observation.json',observation)
    audited=[]
    for row in state.get('selected',state.get('checked_modules',[])):
        module=row['module'];receipt=base/'data'/(module+'-audit.json');r=read(receipt)
        assert sha(receipt)==row['receipt_sha256'] and r['exit_code']==0 and r['status'].startswith('PASS_')
        source=base/'lean'/Path(*module.split('.')).with_suffix('.lean')
        obj=base/'build'/Path(*module.split('.')).with_suffix('.olean')
        log=base/r['log'];snapshot=base/r['source_snapshot']
        assert sha(source)==sha(snapshot)==r['source_sha256']
        assert sha(log)==r['log_sha256'] and sha(obj)==r['olean_sha256']
        for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
        audited.append(dict(module=module,receipt_sha256=sha(receipt),source_sha256=sha(source),object_sha256=sha(obj),log_sha256=sha(log)))
        for path in [receipt,log]:evidence[path.relative_to(ROOT).as_posix()]=path
        receipt_count+=1
    snapshots.append(dict(milestone=int(folder[:3]),status=state['status'],pid=pid,
        completed_contexts=state.get('contexts_checked_by_profile'),checked_modules=len(state.get('checked_modules',[])),
        active=state.get('active'),audited_modules=audited))
save('batch-evidence.json',dict(status='PASS_OBSERVED_PARTIAL_BATCH_RECEIPTS',batches=snapshots,
    scope='Receipt, source, attempt snapshot, object and log hashes checked. Complete batches and final assemblies remain pending. No process restarted or active input changed.'))
archive=HERE/'data/batch-receipts-and-logs.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for name,path in sorted(evidence.items()):z.write(path,name)
save('batch-archive.json',dict(archive='data/batch-receipts-and-logs.zip',sha256=sha(archive),files=[dict(path=name,bytes=path.stat().st_size,sha256=sha(path)) for name,path in sorted(evidence.items())]))
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
c=dict(status='PASS_PAPER116_SOURCE_WITH_COMPILER_UNAVAILABLE',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    prior_checkpoint=prior.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior),paper_revision=116,next_scheduled_paper_revision=126,
    paper_sha256=v['paper_sha256'],verification_sha256=sha(HERE/'data/verification.json'),revision_sha256=sha(HERE/'data/revision.json'),
    compiler_status=read(HERE/'data/compile-final-diagnostic.json')['status'],compile_diagnostic_sha256=sha(HERE/'data/compile-final-diagnostic.json'),
    independent_review_sha256=sha(HERE/'audit/independent-review.md'),batch_evidence_sha256=sha(HERE/'data/batch-evidence.json'),
    named_definitions=1,new_definitions=0,new_lean_checks=0,printed_snakes=13,vertex_pair_checks=118673,
    reference_union_size=1378,reference_entries_discharged=12,remaining_reference_entries=1366,
    maintained_edge_interval=[191,235],conditional_target=234,upper_bound_independent_rebuild_complete=False,
    complete_graph_potential_certificates_checked=False,total310_actual_theorem_checked=False,
    git_refs_before_commit=refs,observed_partial_modules=receipt_count,
    scope='Manuscript synthesis through115, exact source and reused proof checks, immutable partial-batch evidence. No new numerical bound or verified PDF.')
save('checkpoint.json',c)
counts=snapshots[0]['completed_contexts'];count115=snapshots[1]['checked_modules']
summary=f'''The paper is revised through milestone 115, with no new definitions. Its
single named definition is the problem itself. All 135 previous statement
blocks, author metadata, hyperlink settings and appendices are preserved.
Three statement blocks collect checked count restrictions and the shared
excess budget. All 13 printed snakes pass 118,673 pairwise adjacency checks.
Nine reused module receipts, their exact source/object/log bytes and 47
printed axiom reports were checked. No new Lean compiler was launched.

The new local results include the 012340 three-count restriction and the
012314 theorem: middle count at most 2 forces the outer four counts to sum
to at least 19. The paper states their proofs using ordinary count notation.
Twelve of the 1,378 reference entries are discharged; 1,366 remain.

The expanded count-sum family is explicitly conditional. Its finite means
6309/13 and 496 retain integer comparisons 235 and 234. The final attaining
cycles contain no 012345 window, so strengthening only that rule to total
at least 23 leaves their weights and the exact means unchanged. The 23
candidate has native negative evidence and a six-component local equality
witness, without a checked negative certificate or a complete-snake witness.

At this process-verified observation, milestone 104 has
{counts['completed']}/791 completed-profile and {counts['conditional']}/791 conditional-profile
contexts checked. Milestone 115 has {count115}/1397 modules checked. Both
drivers remain active; full certificates and the 012310 actual theorem are
pending. Exact partial receipts and logs are archived in this milestone.

The built-in compiler failed before TeX processing because its Windows
helper could not prepare the preview. No new PDF or page layout is verified.
The maintained interval remains 191 through 235 edges, with the archived
contributor proof and pending complete independent rebuild. Conditional
234, the optimum and 196 remain unresolved. The next full paper revision
is scheduled for milestone 126.
'''
priority='Next research priority: Preserve both live proof batches and verify any final assembly before upgrading its status. Inspect the 26-edge and six-edge replacement cycles in milestone 115; test a shared count restriction on a direction shape they actually contain. Further strengthening only 012345 cannot improve their means. Keep both share profiles in the comparison, and continue the remaining 1,366 reference obligations. Next full paper revision: 126.'
latest='Latest continuation: [milestone 116](milestones/116-paper-revision/README.md) revises the paper through 115 without new definitions, states the checked count restrictions and common excess budget, and distinguishes conditional finite improvements from actual bounds. Source and witness checks pass; the PDF compiler remains unavailable.'
for name in ['README.md','COLLABORATION.md']:
    path=ROOT/name;t=path.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    path.write_text(t,encoding='utf-8')
path=ROOT/'milestones/README.md';t=path.read_text(encoding='utf-8');i=t.index('- [Milestone 115:')
assert '- [Milestone 116:' not in t
path.write_text(t[:i]+'- [Milestone 116: manuscript revision with count-sum results](116-paper-revision/README.md). No new definitions; exact source and witness checks; conditional graph limits; both proof batches preserved.\n\n'+t[i:],encoding='utf-8')
path=ROOT/'RESEARCH_LEDGER.md';t=path.read_text(encoding='utf-8');assert '## Milestone 116:' not in t
path.write_text(t+'\n\n## Milestone 116: manuscript revision\n\n'+summary+'\n'+priority+'\n',encoding='utf-8')
path=ROOT/'handoff/CURRENT_STATUS.md';t=path.read_text(encoding='utf-8');i=t.index('## Milestone 115 checkpoint')
path.write_text(t[:i]+'## Milestone 116 checkpoint\n\n'+summary+'\nEarlier checkpoints below are historical snapshots.\n\n'+t[i:],encoding='utf-8')
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md) and the
[continuation assignment](NEXT_AGENT_PROMPT.md). The latest saved round is
[milestone 116](../milestones/116-paper-revision/README.md).

'''+summary,encoding='utf-8')
path=ROOT/'handoff/NEXT_AGENT_PROMPT.md';t=path.read_text(encoding='utf-8')
path.write_text('''# Continuation after manuscript revision 116

Work in E:/Snake-in-a-box. Read milestone 116 and the current status first.
Use the tensai-bishoujo skill with the user's requested neutral, concise
mathematical prose. Introduce definitions only when essential and repeatedly
used. Preserve the existing symbols and all three authors.

'''+priority+'''

Read the live progress records in milestones 104 and 115 and verify their
processes before any action. Do not start another driver or edit their
active sources, scripts or checker. A partial module count proves no final
contradiction or global theorem. The selected source export for 115 is
already archived; use its documented restoration and verification procedure.

The revised open source is D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex,
mirrored at paper/snake9_research.tex. Keep its editor open and preserve its
hypersetup settings exactly. Revision 116 passed source and witness checks;
the built-in compiler failed before TeX. No current PDF is verified.

Preserve unrelated .gitignore and historical critical-family.json changes.
Fetch before each round and stage only the reviewed milestone manifest.
The optimum remains unresolved; do not mark the research goal complete.

## Earlier continuation record

'''+t,encoding='utf-8')
(ROOT/'paper/README.md').write_text('''# Manuscripts

- `snake9_research.tex`: main paper by Iori Hironaka, Tommy Ma and Steven Zhan.
- `dfs_report/`: the contributor's separate DFS report and generated tables.

The open editor source is D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex.
Edit it in place, then synchronize the repository mirror. Preserve its
author metadata and hyperlink settings. Keep the existing editor open.

Current revision: 116, through research milestone 115. There are 138 statement
blocks, 210 resolved labels and one named definition. No definition was added.
All 135 preceding statement blocks and all appendices are preserved. The 13
printed snakes pass 118,673 pair checks. Editor and mirror are identical.

The new sections present checked count restrictions, the outer-four-sum
theorem, shared excess accounting and conditional graph comparisons.
The maintained interval is 191 through 235 edges; 234 remains conditional.
Twelve reference entries are discharged and 1,366 remain.

The built-in compiler failed before TeX processing. No revision-116 PDF or
page layout is verified. Existing PDFs are earlier snapshots. See
[the revision record](../milestones/116-paper-revision/README.md).
''',encoding='utf-8')
(HERE/'README.md').write_text('''# Milestone 116: revised manuscript and exact evidence boundaries

'''+summary+'''
Read the revised [paper](../../paper/snake9_research.tex),
[independent review](audit/independent-review.md),
[result review](audit/new-results-review.md),
[source verification](data/verification.json), and
[checkpoint](data/checkpoint.json).

The previous paper is preserved byte-for-byte in `data/paper-before.zip`.
`scripts/revise.py` records the revision; it requires the original hash and
will not overwrite a prior backup. `scripts/verify.py` checks the resulting
source, tables, arithmetic, witnesses and reused proof receipts.
`data/batch-receipts-and-logs.zip` preserves the observed successful partial
receipts and logs; source and attempt snapshots stay in their original
milestones, with hashes recorded. Neither batch was restarted or edited.

`scripts/verify_saved.py --verify` checks the frozen package. This milestone
introduces no new solver run, Lean compiler run or global numerical bound.
''',encoding='utf-8')
print(json.dumps(c,indent=2))
