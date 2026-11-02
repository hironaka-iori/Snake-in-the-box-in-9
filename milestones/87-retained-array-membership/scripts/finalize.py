"""Freeze successful owned checks and a delta observation of the live replay."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time,zipfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text())
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as stream:
        for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
receipts=[];audits=0
for module,name in [('RetainedEnumeration','enumeration-audit.json'),('RetainedPredicates','RetainedPredicates-audit.json'),
                    ('NumericRetention','NumericRetention-audit.json'),('ArrayAssembly','ArrayAssembly-audit.json')]:
    p=HERE/'data'/name;r=read(p);assert r['exit_code']==0 and r['status'].startswith('PASS_')
    assert sha(HERE/'lean'/(module+'.lean'))==r['source_sha256']
    assert sha(HERE/'build'/(module+'.olean'))==r.get('olean_sha256',r.get('object_sha256'))
    assert sha(HERE/'logs'/(module+'.log'))==r['log_sha256']
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in r['theorem_audits'])
    audits+=len(r['theorem_audits']);receipts.append(dict(module=module,receipt=name,sha256=sha(p),audits=len(r['theorem_audits'])))
for name in ['array-order-audit.json','retention-equality.json']:
    r=read(HERE/'data'/name);assert r['status'].startswith('PASS_')
    if name=='retention-equality.json':
        assert r['differing_blocks']==0 and r['counts_equal']
        for rel,digest in r['input_sha256'].items():assert sha(ROOT/rel)==digest,rel
        assert sha(HERE/'scripts/check_arrays.py')==r['script_sha256']
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
profile=read(HERE/'data/coverage-profile.json')
assert profile['status']=='PASS_EXACT_MEMBERSHIP_DAG_ROUNDTRIP' and profile['all_block_lists_matched'] and profile['integer_digit_decoder_matches']
assert sha(HERE/'data/coverage-membership-dag.json.gz')==profile['compressed_sha256']
assert sha(HERE/'scripts/profile_coverage.py')==profile['script_sha256']
previous=ROOT/'milestones/86-paper-revision/data/checkpoint.json';old=read(previous)
assert sha(paper)==sha(editor)==old['paper_sha256']
summary=dict(status='PASS_RETENTION_INTERFACES_AND_COMPUTATIONAL_COVERAGE',theorem_audits=audits,modules=receipts,
    array_order_receipt_sha256=sha(HERE/'data/array-order-audit.json'),retention_equality_receipt_sha256=sha(HERE/'data/retention-equality.json'),
    paper_unchanged_sha256=sha(paper),coverage_profile_sha256=sha(HERE/'data/coverage-profile.json'),reference_premises=['AllRefuted6K235','AllRefuted236'],
    remaining_structural_premises=['Concrete Lean RetentionCover for numericKeep and recorded full keys','Concrete source-column identity','Concrete target-column identity'],
    scope='Actual numeric acceptance and conditional saved walk checked. Exact array comparison is computational; no closed Lean finite-table proof, weight interpretation, full potential replay or new global bound.')
(HERE/'data/proof-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists(),'Case7302 completed: refresh pending claims'
for attempt in range(10):
    try:raw=(case/'logs/completion-record.json').read_bytes();live=json.loads(raw);break
    except json.JSONDecodeError:
        if attempt==9:raise
        time.sleep(.1)
(HERE/'data/case7302-completion-observation.json').write_bytes(raw)
prior={r['module']:r for r in old['case7302_successful_rows']};rows=[];new_rows=[]
archive=HERE/'data/case7302-successful-log-snapshot.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as out:
    for row in live['records']:
        if row['exit_code']!=0:continue
        name=row['module'];log=case/'logs'/(name.replace('/','-')+'.log');data=log.read_bytes()
        digest=hashlib.sha256(data).hexdigest();assert 'error:' not in data.decode('utf-8') and 'sorryAx' not in data.decode('utf-8')
        if name in prior:
            checked=prior[name];assert checked['source_sha256']==row['source_sha256'] and checked['log_sha256']==digest
            objhash=checked['object_sha256'];origin='Reused object hash from pinned milestone86; object bytes not rehashed in this delta snapshot'
        else:
            src=case/'lean'/(name+'.lean');obj=Path(live['build'])/(name+'.olean')
            assert sha(src)==row['source_sha256'];objhash=sha(obj);new_rows.append(name)
            origin='Source and object bytes hashed in milestone87'
        info=zipfile.ZipInfo(log.name,(1980,1,1,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;out.writestr(info,data)
        rows.append(dict(module=name,source_sha256=row['source_sha256'],object_sha256=objhash,object_hash_scope=origin,log_sha256=digest,log_archive_member=log.name))
assert set(prior)<={r['module'] for r in rows}
with zipfile.ZipFile(archive) as saved:
    for row in rows:assert hashlib.sha256(saved.read(row['log_archive_member'])).hexdigest()==row['log_sha256']
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7302*' } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
text=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(text) if text else []
if isinstance(processes,dict):processes=[processes]
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
checkpoint=dict(status=summary['status'],recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    theorem_audits=audits,unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence='Inspected contributor theorem and saved audit; no fresh full independent rebuild.',paper_revision=86,next_scheduled_paper_revision=96,paper_sha256=sha(paper),
    git_refs_before_commit=refs,case7302_complete=False,case7302_successful_rows=rows,case7302_new_successful_modules=new_rows,
    case7302_prior_checkpoint=previous.relative_to(ROOT).as_posix(),case7302_prior_checkpoint_sha256=sha(previous),
    case7302_successful_logs_sha256=sha(archive),case7302_observed_processes=processes,proof_replay_tool_session=75639,
    pending_target_cases=[7301,7302,7303,7307,7308],next_task='Certify the concrete finite retention cover/endpoint columns; reuse the checked actual numeric acceptance and saved-walk assembly. Keep reference premises explicit. Continue the existing case7302 replay.')
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(summary['status'],audits,'audits;',len(rows),'successful replay rows,',len(new_rows),'new since86')
