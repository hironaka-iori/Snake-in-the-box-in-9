"""Save an immutable launch snapshot while the separate certificate batch continues."""
from pathlib import Path
import datetime, hashlib, json, re

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
target=HERE/'data/start-checkpoint.json';manifest=HERE/'data/start-manifest.json'
assert not target.exists() and not manifest.exists(),'Launch snapshot is one-shot.'
live=read(HERE/'data/batch-progress.json');assert live['status']=='RUNNING'
plan=read(HERE/'data/plan.json');assert sha(HERE/'data/plan.json')==live['plan_sha256']
assert sha(HERE/'scripts/check.py')==live['checker_sha256']
assert sha(HERE/'scripts/generate.py')==live['generator_sha256']
prior=read(ROOT/'milestones/103-joint-potential-traversal/data/checkpoint.json')
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==prior['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
proofs=[];paths=[]
names=['GraphAssembly104']+[g['module'] for g in live['selected']]
for name in names:
    rp=HERE/'data'/(name+'-audit.json');r=read(rp)
    assert r['status']=='PASS_COMPLETE_BATCH_MODULE' and r['exit_code']==0 and not r['timeout']
    assert sha(HERE/'lean'/(name+'.lean'))==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(HERE/r['log'])==r['log_sha256'] and sha(HERE/'build'/(name+'.olean'))==r['olean_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['theorem_audits'])
    paths.extend([rp,HERE/r['log'],HERE/r['source_snapshot'],(HERE/r['source_snapshot']).parent/'checker.py.txt'])
    proofs.append(dict(module=name,receipt_sha256=sha(rp),theorem_audits=len(r['theorem_audits'])))
for p in (HERE/'lean').glob('*.lean'):
    source=p.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source)
    assert not re.search(r'^def ',source,re.M)
for g in plan['groups']:
    for v in g['variants']:assert sha(HERE/'lean'/(v['module']+'.lean'))==v['source_sha256']
snapshot=dict(status='ACTIVE_COMPLETE_BATCH_LAUNCH_SNAPSHOT',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    batch_state=live,checked_modules_at_snapshot=proofs,plan_sha256=sha(HERE/'data/plan.json'),
    paper_sha256=sha(paper),paper_revision=96,next_scheduled_paper_revision=106,
    unconditional_edge_interval=[191,235],conditional_target=234,
    complete_graph_potential_certificates_checked=False,
    scope='Immutable snapshot of an active batch. Read batch-progress.json for live state. Generated candidates and pending assemblies are not checked results.')
target.write_text(json.dumps(snapshot,indent=2)+'\n')
counts=live['contexts_checked_by_profile']
latest=('Latest continuation: [milestone 104](milestones/104-complete-potential-batch/README.md) runs the complete sequential potential-certificate batch. The graph-assembly theorem is checked. The launch snapshot has '
    f"{counts['completed']} completed-profile and {counts['conditional']} conditional-profile contexts checked; read the live batch record for current progress. The interval remains 191 through 235, with 234 conditional.")
priority=('Next research priority: Let the existing milestone104 batch continue; inspect its live record before any restart. Finish all context certificates, check both graph assemblies, and audit their complete dependency closure. Preserve the pending reference and local-share premises. Paper revision 96 is unchanged; the next full revision is 106.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t)
summary=f'''The complete sequential batch is active. At the saved snapshot, it has
{counts['completed']} completed-profile and {counts['conditional']} conditional-profile
contexts checked. These are snapshot counts, not a claim that the batch is
finished. Read `milestones/104-complete-potential-batch/data/batch-progress.json`
on the running machine, the [saved launch snapshot](../milestones/104-complete-potential-batch/data/start-checkpoint.json),
and [resumption notes](../milestones/104-complete-potential-batch/NEXT.md) before
starting any process. There are 1,157 proposed groups covering all 1,570
previously pending profile/context pairs. Both graph assemblies remain pending.

The general graph-assembly theorem has passed Lean and adds no definitions.
Milestone 103's joint traversal and four matched comparisons are saved and
pushed in commit 04f5fad09c3e6f36568b846050592662174327dc. The preferred methods
are baseline for the completed profile and joint traversal for the conditional
profile, with a separate alternative for timed-out groups. No new global
snake bound is claimed.
'''
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text();i=t.index('## Milestone 103 checkpoint')
p.write_text(t[:i]+'## Milestone 104 active batch\n\n'+summary+'\n'+t[i:])
p=ROOT/'milestones/README.md';t=p.read_text();i=t.index('- [Milestone 103:');assert '- [Milestone 104:' not in t
p.write_text(t[:i]+'- [Milestone 104: complete potential batch](104-complete-potential-batch/README.md). Active sequential certification; general graph assembly checked, full graph results pending.\n\n'+t[i:])
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 104:' not in t
p.write_text(t+'\n\n## Milestone 104: complete batch started\n\n'+latest+'\n\n'+priority+'\n')
p=ROOT/'handoff/README.md';t=p.read_text();t=t.replace('The latest checkpoint is\n[milestone 103](../milestones/103-joint-potential-traversal/README.md).',
    'The current work is the active [milestone 104 batch](../milestones/104-complete-potential-batch/README.md).\nThe last completed checkpoint is [milestone 103](../milestones/103-joint-potential-traversal/README.md).')
t=t.replace('Six contexts per profile remain\ncertified, with 785 per profile pending. No coverage is added by benchmarks.',
    'Milestone 103 certified six contexts per profile. Milestone 104 adds actual\ncontext certificates; consult its live record for current coverage.')
p.write_text(t)
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';t=p.read_text();tail=t[t.index('## Global evidence and remaining assumptions'):]
tail=tail.replace('milestones/103-joint-potential-traversal/scripts/check.py','milestones/104-complete-potential-batch/scripts/check.py')
tail=tail.replace('environment reuses milestone 102 and the milestone 98 support overlay.','environment reuses milestone 103 and the milestone 98 support overlay.')
p.write_text('''# Continuation assignment

Continue the existing milestone104 complete batch in `E:/Snake-in-a-box`.
First read its README.md, NEXT.md, data/batch-progress.json and the latest
batch log. Inspect the recorded processes and lock files. The batch may still
be running; do not start another or edit any active proof source or checker.

'''+summary+'''
The complete proposed queue and all source hashes are in data/plan.json.
Successful Lean receipts supply the checked status. After every group passes,
the driver generates and checks AllCompleted104 and AllConditional104. An
ordinary proof error stops the driver; a timeout tries the separate alternative.
Follow NEXT.md to resume. Do not rerun prepare.py over the active environment.

The graph-assembly theorem is
Snake9.GraphAssembly104.graphCheck_of_saved_blocks. It uses context certificates
for entries of the original savedBlockClasses, and proves the original
graphCheck. Missing contexts use the existing semantic theorem. No new
definition or additional arbitrary-snake premise was introduced.

Finish the complete graph audit before publishing completion of this batch.
The research goal and the conditional local refutations remain unresolved.

'''+tail)
paths += list((HERE/'lean').glob('*.lean'))+list((HERE/'scripts').glob('*.py'))+list((HERE/'audit').glob('*.md'))
paths += [HERE/p for p in ['README.md','NEXT.md','.gitattributes','data/environment.json','data/plan.json','data/start-checkpoint.json']]
# Preserve terminal unsuccessful attempts; exclude mutable current run records and logs.
for p in (HERE/'logs').glob('*-record.json'):
    r=read(p)
    if r['exit_code']!=0 or r['timeout']:
        paths += [p,HERE/r['log'],HERE/r['source_snapshot'],(HERE/r['source_snapshot']).parent/'checker.py.txt']
for p in (HERE/'logs').glob('check-run-*.json'):
    try:r=read(p)
    except json.JSONDecodeError:continue
    if r['status'] in ['STOPPED','PASS_REQUESTED_MODULES']:paths.append(p)
paths += [ROOT/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
    'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(paths))]
manifest.write_text(json.dumps(dict(status='SAVED_ACTIVE_BATCH_LAUNCH',files=rows,
    scope='Immutable sources, launch snapshot and selected checked evidence. Live progress, future receipts and active logs are intentionally outside this launch manifest.'),indent=2)+'\n')
print('SAVED_ACTIVE_BATCH_LAUNCH',len(rows),'files;',counts)
