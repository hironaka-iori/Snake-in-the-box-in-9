"""Freeze successful replay rows and the current paper evidence without changing the live job."""
from pathlib import Path
import datetime,hashlib,json,shutil,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7305'
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
for folder in ['data','replay-snapshot/logs']:(HERE/folder).mkdir(parents=True,exist_ok=True)
for attempt in range(5):
    try:
        raw=(CASE/'logs/completion-record.json').read_bytes();live_record=json.loads(raw);break
    except json.JSONDecodeError:
        if attempt==4:raise
        time.sleep(.1)
rows=[]
for row in live_record['records']:
    if row['exit_code']!=0:continue
    name=row['module'];source=CASE/'lean'/(name+'.lean');obj=Path(live_record['build'])/(name+'.olean')
    log=CASE/'logs'/(name.replace('/','-')+'.log')
    assert sha(source)==row['source_sha256']
    for dep,digest in row.get('dependencies',{}).items():assert sha(CASE/'lean'/(dep+'.lean'))==digest
    assert obj.exists() and log.exists()
    contents=log.read_text(encoding='utf-8')
    assert 'error:' not in contents and 'sorryAx' not in contents
    dest=HERE/'replay-snapshot/logs'/log.name;shutil.copyfile(log,dest)
    rows.append(dict(row,object_sha256=sha(obj),log_sha256=sha(dest),snapshot_log=dest.relative_to(HERE).as_posix()))
selection=json.loads((CASE/'data/lrat-slice-selection.json').read_text())
assert sha(CASE/'certificates/share7305.lrat')==selection['selected_lrat_sha256']
snapshot=dict(status='PARTIAL_REPLAY_COMPLETED_MODULES_ONLY',records=rows,
 observed_live_record_sha256=hashlib.sha256(raw).hexdigest(),selected_lrat_sha256=selection['selected_lrat_sha256'],
 completed_check_modules=sum('/Check' in r['module'] for r in rows),
 completed_data_modules=sum('/Data' in r['module'] for r in rows),
 scope='Frozen successful source/object/log-matched rows only. The final refutation and local share theorem remain pending.')
(HERE/'replay-snapshot/record.json').write_text(json.dumps(snapshot,indent=2)+'\n',encoding='utf-8')
cmd="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7305*' } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
process_text=subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True).strip()
processes=json.loads(process_text) if process_text else []
if isinstance(processes,dict):processes=[processes]
verification=json.loads((HERE/'data/verification.json').read_text())
arithmetic=json.loads((HERE/'data/arithmetic-audit.json').read_text())
assert verification['status']=='PASS_SOURCE_AND_MATHEMATICAL_CHECKS'
assert arithmetic['status']=='PASS_PAPER_CONDITIONAL_ARITHMETIC'
assert sha(HERE/'lean/PaperArithmetic.lean')==arithmetic['source_sha256']
assert sha(HERE/'build/PaperArithmetic.olean')==arithmetic['olean_sha256']
assert sha(HERE/'logs/PaperArithmetic.log')==arithmetic['log_sha256']
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)==verification['paper_sha256']
refs={name:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',name],cwd=ROOT,text=True).strip() for name in ['HEAD','origin/main','origin/research/unconditional-241']}
record=dict(status='PAPER76_SOURCE_VERIFIED_COMPILE_BLOCKED',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 paper_sha256=sha(paper),revision=76,unconditional_edge_interval=[191,235],conditional_target=234,
 new_lean_arithmetic_audits=6,previous_paper_statements=116,current_paper_statements=123,
 printed_snakes=13,vertex_pair_checks=118673,compiler='Blocked before compilation by app execution environment; no new PDF verified',
 git_refs=refs,replay_completed_modules=len(rows),replay_check_modules=snapshot['completed_check_modules'],
 replay_snapshot_sha256=sha(HERE/'replay-snapshot/record.json'),observed_processes=processes,tool_session_id=41012,
 process_scope='Historical observation only. Revalidate the current process before any restart. Do not start a duplicate completion driver.',
 completed_stronger_share_cases=[7300,7304,7306],case7305_final_theorem=False,
 next_steps=['Finish the existing case7305 replay and complete geometric/reversal audit',
             'Complete the other five local targets and exact actual-snake graph walk',
             'Replay the full potential and compose the global theorem',
             'Recompile the same editor source when the app compiler is available'])
(HERE/'data/checkpoint.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(record['status'],len(rows),'completed replay rows;',snapshot['completed_check_modules'],'large checks;',len(processes),'matching processes')
