"""Freeze exact partial-proof evidence and observe, without restarting, its driver."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
comparison=read(HERE/'data/comparison-audit.json');assert comparison['status']=='PASS_EXACT_SINGLE_TARGET_COMPARISON'
for path,digest in comparison['inputs'].items():assert sha(ROOT/path)==digest
arith=read(HERE/'data/lean-audit.json');assert arith['status']=='PASS_SINGLE_TARGET_CONDITIONAL_ARITHMETIC'
assert arith['comparison_audit_sha256']==sha(HERE/'data/comparison-audit.json')
for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','object_sha256'),('logs','.log','log_sha256')]:
    assert sha(HERE/folder/('ConditionalTarget'+ext))==arith[key]
assert len(arith['theorem_audits'])==3
pending=read(CASE/'data/pending-checkpoint.json')
assert pending['status']=='SEMANTICS_CHECKED_REFUTATION_REPLAY_PENDING'
assert pending['case_number']==7302 and pending['target_share']==20 and pending['pattern']=='012034'
assert len(pending['compiled_modules'])==127
assert not (CASE/'data/proof-audit.json').exists(),'Case finished: audit and integrate instead of saving a pending checkpoint'
for rel,digest in pending['source_sha256'].items():assert sha(CASE/rel)==digest
for row in pending['archives']:
    assert sha(CASE/row['path'])==row['sha256']
    transport=row.get('parts',[row])
    for part in transport:
        assert part['bytes']<100*1024*1024 and sha(CASE/part['path'])==part['sha256']
for rel,digest in pending['receipts'].items():assert sha(CASE/rel)==digest
successful={r['module']:r for r in pending['compiled_modules']}
record=CASE/'logs/completion-record.json'
if record.exists():
    for attempt in range(10):
        try:raw=record.read_bytes();live=json.loads(raw);break
        except json.JSONDecodeError:
            if attempt==9:raise
            time.sleep(.1)
    (HERE/'data/replay-completion-record.json').write_bytes(raw)
    for r in live['records']:
        name=r['module'];src=CASE/'lean'/(name+'.lean');obj=Path(live['build'])/(name+'.olean')
        log=CASE/'logs'/(name.replace('/','-')+'.log')
        if r['exit_code']!=0 or not obj.exists() or sha(src)!=r['source_sha256']:continue
        if any(sha(CASE/'lean'/(n+'.lean'))!=h for n,h in r['dependencies'].items()):continue
        text=log.read_text();assert all(x not in text for x in ['error:','sorryAx','failed to delete'])
        successful[name]=dict(module=name,source=src.relative_to(CASE).as_posix(),source_sha256=sha(src),
            object=obj.relative_to(CASE).as_posix(),object_sha256=sha(obj),log=log.relative_to(CASE).as_posix(),log_sha256=sha(log))
observation=dict(status='PARTIAL_REPLAY_OBSERVATION',successful_modules=len(successful),
    source_modules=len(pending['source_sha256']),modules=list(successful.values()),
    scope='Snapshot of source/object/log-matched successful modules. Not the final local theorem; active progress may be newer.')
(HERE/'data/replay-observation.json').write_text(json.dumps(observation,indent=2)+'\n')
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7302*' } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
text=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(text) if text else []
if isinstance(processes,dict):processes=[processes]
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
      for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
selection=read(CASE/'data/lrat-slice-selection.json')
probe=read(HERE/'stronger-probe/result.json');assert probe['status']=='UNKNOWN'
checkpoint=dict(status='PARTIAL_SHARE20_SEMANTICS_AND_EXACT_CONDITIONAL_COMPARISON',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),git_refs_before_commit=refs,
    unconditional_edge_interval=[191,235],upper_bound_evidence='Inspected contributor theorem and saved audit; no fresh full independent rebuild.',
    conditional_target=234,case7302_complete=False,remaining_local_share_cases=[7301,7302,7303,7307,7308],
    conditional_mean='9259/19',conditional_scaled_range=11301,conditional_scale=19,conditional_integer_comparison=235,
    arithmetic_audits=3,semantic_modules=127,replay_successful_modules=len(successful),replay_source_modules=len(pending['source_sha256']),
    selected_refutation={k:selection['after'][k] for k in ['lemmas','hints','slots','segments','word_bits']},
    observed_processes=processes,proof_replay_tool_session=75639,
    process_scope='Historical process observation. Session IDs belong to this execution context. Inspect the actual handle or process before resuming; do not duplicate a running driver.',
    stronger_floor32_probe='UNKNOWN; no candidate returned; no proof or counterexample.',
    paper_revision=76,next_scheduled_paper_revision=86,paper_sha256=sha(paper),
    evidence_sha256={str(p.relative_to(ROOT)):sha(p) for p in [HERE/'data/comparison-audit.json',HERE/'data/lean-audit.json',
      HERE/'data/replay-observation.json',CASE/'data/pending-checkpoint.json',HERE/'audit/preparation-review.md',
      HERE/'audit/comparison-review.md',HERE/'audit/preservation-review.md',HERE/'stronger-probe/result.json']})
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(checkpoint['status'],len(successful),'of',len(pending['source_sha256']),'modules;',len(processes),'observed processes')
