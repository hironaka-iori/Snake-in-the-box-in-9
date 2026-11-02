"""Verify completed history-retention evidence and freeze a live-replay observation."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=ROOT/'milestones/79-retained-edge-guards'
modules=['HistoryWindow','HistoryRealizations','HistoryUnique','HistoryCountSupport',
    'TerminalCount','CountPhase04','CountPhase29','HistoryExclusions']
rows=[]
for name in modules:
    path=HERE/'data'/f'{name}-audit.json';r=read(path)
    assert r['status']=='PASS_LEAN_MODULE' and r['exit_code']==0
    for sub,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(HERE/sub/(name+ext))==r[key]
    assert not re.search(r'\b(sorry|admit|native_decide)\b',(HERE/'lean'/f'{name}.lean').read_text())
    assert r['inherited_summary_sha256']==sha(old/'data/proof-summary.json')
    for dep,digest in r['dependencies'].items():
        base=old if dep=='IntervalGuards' else HERE
        assert sha(base/'data'/f'{dep}-audit.json')==digest
    if 'compatible_count_sources_sha256' in r:assert sha(HERE/'data/compatible-count-sources.json')==r['compatible_count_sources_sha256']
    if 'position_support_receipt_sha256' in r:
        assert sha(ROOT/'milestones/81-recovered-short-rule-retention/data/PositionTransfer-audit.json')==r['position_support_receipt_sha256']
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['theorem_audits'])
    rows.append(dict(module=name,receipt=path.relative_to(HERE).as_posix(),sha256=sha(path),audits=len(r['theorem_audits'])))
assert sum(r['audits'] for r in rows)==38
comparison=read(HERE/'data/filter-comparison.json');assert comparison['status']=='PASS_EXACT_THREE_HISTORY_FILTER_COMPARISON'
for rel,digest in comparison['inputs'].items():assert sha(ROOT/rel)==digest
realizations=read(HERE/'data/realizations.json');assert realizations['canonical_induced_eleven_shapes']==11162
for rel,digest in realizations['inputs'].items():assert sha(ROOT/rel)==digest
comp=read(HERE/'data/compatible-count-sources.json')
for rel,digest in comp['source_sha256'].items():assert sha(ROOT/rel)==digest
assert sha(HERE/'lean/HistoryCountSupport.lean')==comp['support_source_sha256']
for name,row in comp['roots'].items():
    assert sha(ROOT/row['source'])==row['source_sha256']
    assert sha(HERE/'lean'/(name+'.lean'))==row['adapted_source_sha256']
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
result=dict(status='PASS_THREE_HISTORY_EXCLUSION_RETENTION',receipts=rows,printed_theorem_audits=38,
    inherited_summary_sha256=sha(old/'data/proof-summary.json'),
    compatible_count_sources_sha256=sha(HERE/'data/compatible-count-sources.json'),
    filter_comparison_sha256=sha(HERE/'data/filter-comparison.json'),realizations_sha256=sha(HERE/'data/realizations.json'),
    limitations=['Inherited window/direction environment reused; no clean full dependency rebuild.',
      'Reference union and retained-array membership remain.',
      'Credit interpretation and complete potential replay remain.',
      'Five target local share theorems remain; no new global numerical bound.'])
(HERE/'data/proof-summary.json').write_text(json.dumps(result,indent=2)+'\n')
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
for attempt in range(10):
    try:raw=(case/'logs/completion-record.json').read_bytes();live=json.loads(raw);break
    except json.JSONDecodeError:
        if attempt==9:raise
        time.sleep(.1)
(HERE/'data/case7302-completion-observation.json').write_bytes(raw)
checked={}
for r in live['records']:
    if r['exit_code']!=0:continue
    name=r['module'];source=case/'lean'/(name+'.lean');obj=Path(live['build'])/(name+'.olean')
    log=case/'logs'/(name.replace('/','-')+'.log')
    assert sha(source)==r['source_sha256'] and obj.exists()
    assert all(sha(case/'lean'/(n+'.lean'))==h for n,h in r['dependencies'].items())
    assert not any(s in log.read_text() for s in ['error:','sorryAx'])
    checked[name]=dict(source_sha256=sha(source),object_sha256=sha(obj),log_sha256=sha(log))
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7302*' } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
rawprocess=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(rawprocess) if rawprocess else []
if isinstance(processes,dict):processes=[processes]
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
  for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
checkpoint=dict(status=result['status'],recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    git_refs_before_commit=refs,unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence='Inspected contributor theorem and saved audit; no fresh full independent rebuild.',
    paper_revision=76,next_scheduled_paper_revision=86,paper_sha256=sha(paper),
    printed_theorem_audits=38,history_rules=3,case7305_complete=True,
    case7302_complete=(case/'data/proof-audit.json').exists(),remaining_local_share_cases=[7301,7302,7303,7307,7308],
    case7302_observed_successes=checked,case7302_live_processes=processes,proof_replay_tool_session=75639,
    process_scope='Historical process and successful-row observation. Inspect actual handle/process before resuming; do not duplicate the case7302 driver.',
    completed_share_model_mean='483',single_pending_share_model_mean='9259/19',
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),independent_review_sha256=sha(HERE/'audit/review.md'))
assert not checkpoint['case7302_complete'],'The case finished: update its status before saving this checkpoint'
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(result['status'],'38 audits;',len(checked),'source-matched case7302 progress records;',len(processes),'live processes observed')
