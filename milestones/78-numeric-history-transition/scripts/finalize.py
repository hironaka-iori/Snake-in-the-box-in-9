"""Validate checked interfaces and freeze a timestamped replay observation."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name in ['IndexSelector','NumericTransition','CountGeometry','StateWalk']:
    path=HERE/'data'/f'{name}-audit.json';r=json.loads(path.read_text())
    assert r['status']=='PASS_LEAN_MODULE'
    for sub,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(HERE/sub/(name+suffix))==r[key]
    for dep,digest in r['dependencies'].items():assert sha(HERE/'data'/f'{dep}-audit.json')==digest
    rows.append(dict(module=name,receipt=path.relative_to(HERE).as_posix(),sha256=sha(path),audits=len(r['theorem_audits'])))
comparison=json.loads((HERE/'data/builder-comparison.json').read_text())
assert comparison['status']=='PASS_EXACT_BUILDER_SELECTOR_COMPARISON'
assert sha(HERE/'data/history-next.u8')==comparison['output_sha256']
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
result=dict(status='PASS_NUMERIC_HISTORY_AND_ENCODED_STATE_SEQUENCE',receipts=rows,
    printed_theorem_audits=sum(r['audits'] for r in rows),builder_comparison_sha256=sha(HERE/'data/builder-comparison.json'),
    paper_sha256=sha(paper),limitations=['Existing hash-matched support reused; full dependency closure not rebuilt.',
    'Retained-edge membership, exclusion/credit interpretation and complete potential proof remain.',
    'No new numerical bound or local share theorem is claimed by this interface.'])
(HERE/'data/proof-summary.json').write_text(json.dumps(result,indent=2)+'\n')
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7305'
for attempt in range(5):
    try:
        raw=(CASE/'logs/completion-record.json').read_bytes();replay=json.loads(raw);break
    except json.JSONDecodeError:
        if attempt==4:raise
        time.sleep(.1)
(HERE/'data/replay-record.json').write_bytes(raw)
successful={r['module']:r for r in replay['records'] if r['exit_code']==0}
checked=[]
for name,r in sorted(successful.items()):
    src=CASE/'lean'/(name+'.lean');obj=Path(replay['build'])/(name+'.olean')
    log=CASE/'logs'/(name.replace('/','-')+'.log')
    assert sha(src)==r['source_sha256']
    for dep,digest in r.get('dependencies',{}).items():assert sha(CASE/'lean'/(dep+'.lean'))==digest
    text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
    checked.append(dict(module=name,source_sha256=sha(src),object_sha256=sha(obj),log_sha256=sha(log)))
(HERE/'data/replay-evidence.json').write_text(json.dumps(dict(status='PARTIAL_SUCCESSFUL_MODULE_OBSERVATION',
    modules=checked,scope='Hash checks on existing local files; final local theorem pending. No terminal status inferred.'),indent=2)+'\n')
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7305*' } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
text=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(text) if text else []
if isinstance(processes,dict):processes=[processes]
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
    for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
checkpoint=dict(status=result['status'],recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    git_refs=refs,unconditional_edge_interval=[191,235],conditional_target=234,paper_revision=76,
    paper_sha256=sha(paper),printed_theorem_audits=result['printed_theorem_audits'],
    replay_successful_modules=len(checked),replay_record_sha256=sha(HERE/'data/replay-record.json'),
    observed_processes=processes,tool_session_id=41012,case7305_final_theorem=False,
    process_scope='Historical observation; inspect actual processes before any restart. Use one completion driver.')
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(result['status'],result['printed_theorem_audits'],'audits;',len(checked),'replay rows;',len(processes),'processes')
