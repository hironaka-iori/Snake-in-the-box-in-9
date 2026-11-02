"""Verify current proofs and freeze a read-only snapshot of the other live run."""
from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=['DirectionTables','PrunedEnumeration','PrunedAssembly']+[f'CoverageTail{i:02d}' for i in range(7)]+[
    f'CoverageLeaf{i:02d}' for i in range(12)]+[
    'CoverageAssembly','DirectionCoverage','ActualDirectionIds',
    'LookupDefinitions']+[f'LookupChunk{i:02d}' for i in range(6)]+[
    'LookupTableCheck','HistoryCompatibilityData','HistoryShape']
receipts=[]
for name in modules:
    path=HERE/'data'/f'{name}-audit.json';r=json.loads(path.read_text())
    assert r['status']=='PASS_LEAN_MODULE'
    assert sha(HERE/'lean'/f'{name}.lean')==r['source_sha256']
    assert sha(HERE/'build'/f'{name}.olean')==r['olean_sha256']
    assert sha(HERE/'logs'/f'{name}.log')==r['log_sha256']
    for dep,digest in r['dependencies'].items():
        assert sha(HERE/'data'/f'{dep}-audit.json')==digest
    receipts.append(dict(module=name,receipt=path.relative_to(HERE).as_posix(),
        sha256=sha(path),audits=len(r['theorem_audits'])))
hpath=HERE/'history/data/proof-audit.json';h=json.loads(hpath.read_text())
assert h['status']=='PASS_NUMERIC_HISTORY_AND_SIGNATURE_EQUIVALENCE'
assert sha(HERE/'history/lean/NumericHistory.lean')==h['source_sha256']
assert sha(HERE/'history/build/NumericHistory.olean')==h['olean_sha256']
assert sha(HERE/'history/logs/NumericHistory.log')==h['log_sha256']
receipts.append(dict(module='NumericHistory',receipt=hpath.relative_to(HERE).as_posix(),
    sha256=sha(hpath),audits=len(h['theorems'])))
table_audit=json.loads((HERE/'audit/table-audit.json').read_text())
assert table_audit['status']=='PASS_ORDERED_DIRECTION_AND_HISTORY_TABLE_AUDIT'
for source in (HERE/'lean').glob('*.lean'):
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text())
paper=ROOT/'paper/snake9_research.tex'
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
proof=dict(status='PASS_DIRECTION_AND_HISTORY_SHAPE_INTERFACES',receipts=receipts,
    printed_theorem_audits=sum(r['audits'] for r in receipts),paper_sha256=sha(paper),
    limitations=['Inherited compiled support reused with hash checks; no complete clean rebuild.',
    'No concrete numeric history-update equality, full count-state or retained-edge interpretation.',
    'No new local share theorem, complete potential replay or improved numerical bound.'])
(HERE/'data/proof-summary.json').write_text(json.dumps(proof,indent=2)+'\n')
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7305'
for attempt in range(5):
    try:
        raw=(CASE/'logs/completion-record.json').read_bytes();live=json.loads(raw);break
    except json.JSONDecodeError:
        if attempt==4:raise
        time.sleep(.1)
folder=HERE/'replay-snapshot/logs';folder.mkdir(parents=True,exist_ok=True)
unique={r['module']:r for r in live['records'] if r['exit_code']==0}
rows=[]
for name,r in sorted(unique.items()):
    src=CASE/'lean'/(name+'.lean');obj=Path(live['build'])/(name+'.olean')
    assert sha(src)==r['source_sha256']
    for dep,digest in r.get('dependencies',{}).items():
        assert sha(CASE/'lean'/(dep+'.lean'))==digest
    log=CASE/'logs'/(name.replace('/','-')+'.log')
    text=log.read_text(encoding='utf-8');assert 'error:' not in text and 'sorryAx' not in text
    dest=folder/log.name;shutil.copyfile(log,dest)
    rows.append(dict(r,object_sha256=sha(obj),log_sha256=sha(dest),
        snapshot_log=dest.relative_to(HERE).as_posix()))
selected=json.loads((CASE/'data/lrat-slice-selection.json').read_text())
assert sha(CASE/'certificates/share7305.lrat')==selected['selected_lrat_sha256']
snapshot=dict(status='PARTIAL_REPLAY_COMPLETED_MODULES_ONLY',records=rows,
    observed_live_record_sha256=hashlib.sha256(raw).hexdigest(),
    selected_lrat_sha256=selected['selected_lrat_sha256'],
    completed_check_modules=sum('/Check' in r['module'] for r in rows),
    completed_data_modules=sum('/Data' in r['module'] for r in rows),
    scope='Successful hash-matched modules only; final local theorem remains pending.')
(HERE/'replay-snapshot/record.json').write_text(json.dumps(snapshot,indent=2)+'\n')
cmd="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7305*' } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
text=subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True).strip()
processes=json.loads(text) if text else []
if isinstance(processes,dict):processes=[processes]
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],
    cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
checkpoint=dict(status=proof['status'],recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    git_refs=refs,paper_revision=76,paper_sha256=sha(paper),printed_theorem_audits=proof['printed_theorem_audits'],
    unconditional_edge_interval=[191,235],conditional_target=234,exact_optimum_unresolved=True,
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    replay_snapshot_sha256=sha(HERE/'replay-snapshot/record.json'),
    successful_replay_modules=len(rows),completed_large_checks=snapshot['completed_check_modules'],
    tool_session_id=41012,observed_processes=processes,case7305_final_theorem=False,
    scope='Process observation is historical. Inspect actual processes before restarting; one driver per case.')
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(proof['status'],proof['printed_theorem_audits'],'audits;',len(rows),'replay modules;',
    snapshot['completed_check_modules'],'large checks;',len(processes),'observed processes')
