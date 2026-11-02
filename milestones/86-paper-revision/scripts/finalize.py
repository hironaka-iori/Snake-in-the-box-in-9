"""Freeze the paper evidence and a nonintrusive snapshot of the continuing replay."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time,zipfile

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
verification=read(HERE/'data/verification.json');logic=read(HERE/'data/logic-audit.json')
assert verification['status']=='PASS_PAPER86_SOURCE_AND_MATHEMATICS'
assert logic['status']=='PASS_PAPER86_LOGIC'
bonus=read(HERE/'data/bonus-audit.json');assert bonus['status']=='PASS_PAPER86_LOGIC'
assert sha(paper)==sha(editor)==verification['paper_sha256']==read(HERE/'data/revision.json')['paper_sha256']
for rel,digest in verification['cited_receipt_hashes'].items():assert sha(ROOT/rel)==digest
review=HERE/'audit/post-edit-review.md';assert verification['paper_sha256'] in review.read_text()
compile_record=read(HERE/'data/editor-compile-final.json');assert compile_record['paper_sha256']==sha(paper)
raw_compile=compile_record['result'];payload=json.loads(raw_compile['content'][0]['text'])
assert payload['kind']=='compile-failed'
assert 'Compiler helper failed' in payload['diagnostics']['log']
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists(),'Case7302 completed: refresh all pending claims before checkpointing'
for attempt in range(10):
    try:raw=(case/'logs/completion-record.json').read_bytes();live=json.loads(raw);break
    except json.JSONDecodeError:
        if attempt==9:raise
        time.sleep(.1)
(HERE/'data/case7302-completion-observation.json').write_bytes(raw)
rows=[]
archive=HERE/'data/case7302-successful-log-snapshot.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as out:
    for r in live['records']:
        if r['exit_code']!=0:continue
        name=r['module'];source=case/'lean'/(name+'.lean');obj=Path(live['build'])/(name+'.olean')
        log=case/'logs'/(name.replace('/','-')+'.log')
        assert sha(source)==r['source_sha256'] and obj.exists()
        assert all(sha(case/'lean'/(n+'.lean'))==h for n,h in r['dependencies'].items())
        logbytes=log.read_bytes();text=logbytes.decode('utf-8')
        assert 'error:' not in text and 'sorryAx' not in text
        info=zipfile.ZipInfo(log.name,(1980,1,1,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
        out.writestr(info,logbytes)
        rows.append(dict(module=name,source_sha256=sha(source),object_sha256=sha(obj),
                         log_sha256=hashlib.sha256(logbytes).hexdigest(),log_archive_member=log.name))
with zipfile.ZipFile(archive) as saved:
    assert len(saved.namelist())==len(rows)
    for row in rows:assert hashlib.sha256(saved.read(row['log_archive_member'])).hexdigest()==row['log_sha256']
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7302*' } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
process_text=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(process_text) if process_text else []
if isinstance(processes,dict):processes=[processes]
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
      for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
record=dict(status='PAPER86_SOURCE_VERIFIED_COMPILER_UNAVAILABLE',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    paper_sha256=sha(paper),paper_revision=86,next_scheduled_paper_revision=96,
    unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence='Inspected contributor theorem and saved audit; no fresh full independent rebuild.',
    previous_statements=123,current_statements=130,changed_prior_statement_labels=['thm:countfree-completed'],
    new_propositions=6,new_definitions=1,new_lean_checks=14,labels=190,printed_snakes=13,vertex_pair_checks=118673,
    metadata_preserved=True,appendix_body_preserved=True,git_refs_before_commit=refs,
    compiler='Failed before source compilation; no new PDF or visual layout verified.',
    verification_sha256=sha(HERE/'data/verification.json'),logic_audit_sha256=sha(HERE/'data/logic-audit.json'),
    bonus_audit_sha256=sha(HERE/'data/bonus-audit.json'),
    editor_compile_sha256=sha(HERE/'data/editor-compile-final.json'),post_edit_review_sha256=sha(review),
    completed_target_cases=[7300,7304,7305,7306],pending_target_cases=[7301,7302,7303,7307,7308],
    case7302_complete=False,case7302_successful_rows=rows,case7302_successful_logs_sha256=sha(archive),
    case7302_observed_processes=processes,proof_replay_tool_session=75639,
    process_scope='Historical observation of the existing driver. Inspect its live handle before continuation; never restart from an observation timeout.',
    next_proof_task='Exact retained-array membership, with the two reference-catalogue premises explicit until closed dependencies are available.')
(HERE/'data/checkpoint.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],'130 statements; 14 new Lean checks;',len(rows),'successful replay rows saved')
