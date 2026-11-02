"""Freeze milestone93 evidence and immutable observations of continuing jobs."""
from pathlib import Path
from fractions import Fraction
import datetime, hashlib, json, re, subprocess, time, zipfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
PREV=HERE.parent/'92-full-witness-batch';GEO=HERE.parent/'89-shared-cover-certification'
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def stable(p):
    for i in range(10):
        raw=p.read_bytes()
        try:return raw,json.loads(raw)
        except json.JSONDecodeError:
            if i==9:raise
            time.sleep(.1)
def save(name,value):
    (HERE/'data'/name).write_text(json.dumps(value,indent=2)+'\n')
def check_module(base,rp):
    raw,r=stable(rp);name=r['module']
    assert r['exit_code']==0 and r['status'].startswith('PASS_')
    src=base/'lean'/(name+'.lean');log=base/'logs'/(name+'.log')
    assert sha(src)==r['source_sha256'] and sha(base/'build'/(name+'.olean'))==r['olean_sha256']
    assert sha(log)==r['log_sha256']
    assert len(r['theorem_audits'])==src.read_text().count('#print axioms')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    return dict(module=name,receipt=rp.relative_to(ROOT).as_posix(),receipt_sha256=sha(rp),
                theorem_audits=len(r['theorem_audits']),source_sha256=r['source_sha256'],
                object_sha256=r['olean_sha256'],log_sha256=r['log_sha256'])

oldpath=PREV/'data/checkpoint.json';old=read(oldpath)
auditpath=HERE/'data/PotentialComparison-audit.json';audit=read(auditpath)
assert audit['exit_code']==0 and audit['status']=='PASS_RATIONAL_POTENTIAL_COMPARISON'
for p,key in [(HERE/'lean/PotentialComparison.lean','source_sha256'),
              (HERE/'scripts/check_comparison.py','checker_sha256'),
              (HERE/'build/PotentialComparison.olean','olean_sha256'),
              (HERE/audit['log'],'log_sha256')]:assert sha(p)==audit[key],p
assert len(audit['theorem_audits'])==7
for r in audit['theorem_audits']:assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'}
review=read(HERE/'data/range-certificate-review.json')
for r in review['models']:
    p=HERE/'data'/(r['model']+'-range-certificate.json');c=read(p)
    assert sha(p)==r['certificate_sha256']
    M=Fraction(c['mean']);R=Fraction(c['potential_range']);k=c['path_edges'];C=c['path_weight']
    assert R==k*M-C and Fraction(c['cycle_weight'],c['cycle_edges'])==M
    B=(1098960+8*M+R)/(4200+M)
    assert str(B)==r['comparison_bound'] and k+8<=B
    assert 1098960-C-4200*(k+8)==r['joint_condition_numerator']
    assert r['all_array_edges_checked']==4947008

prior_geometry={r['module']:r for r in read(PREV/'data/geometry-observation.json')['modules']}
prior_witness={r['module']:r for r in read(PREV/'data/proof-summary.json')['modules']}
observations={};archive=HERE/'data/completed-batch-delta.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as out:
    for label,base,prior,pattern in [
        ('geometry',GEO,prior_geometry,r'(?:Balanced\d{3}|Cover\d{3})(?:Data|Checks)-audit.json'),
        ('witness',PREV,prior_witness,r'Witness\d{3}(?:Data|Checks)-audit.json')]:
        rows=[];new=[]
        for rp in sorted((base/'data').glob('*-audit.json')):
            if not re.fullmatch(pattern,rp.name):continue
            name=rp.name.removesuffix('-audit.json')
            if name in prior:
                assert sha(rp)==prior[name]['receipt_sha256']
                row=prior[name]
            else:
                row=check_module(base,rp);new.append(name)
                for p in [rp,base/'logs'/(name+'.log'),base/'logs'/(name+'-record.json')]:
                    if p.exists():
                        info=zipfile.ZipInfo(p.relative_to(ROOT).as_posix(),(1980,1,1,0,0,0))
                        info.compress_type=zipfile.ZIP_DEFLATED;out.writestr(info,p.read_bytes())
            rows.append(row)
        prefix='Balanced' if label=='geometry' else 'Witness'
        classes=sorted(int(m.group(1)) for r in rows if (m:=re.fullmatch(prefix+r'(\d{3})Checks',r['module'])))
        observations[label]=dict(classes=classes,modules=rows,new_modules=new,
                                  new_audits=sum(r['theorem_audits'] for r in rows if r['module'] in new))
save('batch-progress-observation.json',observations)

run_observations=[]
paths=[PREV/'data/witness-batch-active.json',*sorted((PREV/'logs').glob('witness-batch-run-*.json')),
       *sorted((GEO/'logs').glob('balanced-cover-run-*.json')),GEO/'logs/case7302-unique-resume-run.json']
for p in paths:
    raw,r=stable(p);target=HERE/'data'/('snapshot-'+p.name);target.write_bytes(raw)
    run_observations.append(dict(original=p.relative_to(ROOT).as_posix(),snapshot=target.name,sha256=sha(target),
                                 status=r.get('status'),active=r.get('active'),pid=r.get('pid')))
raw,live=stable(CASE/'logs/completion-record.json')
(HERE/'data/case7302-completion-observation.json').write_bytes(raw)
assert live['records'][-1]['module']=='LocalWindowUnsat/ShareWindow7302/Check1'
assert live['records'][-1]['exit_code']=='TIMEOUT'
assert not (CASE/'data/proof-audit.json').exists()
prior={r['module']:r for r in old['case7302_successful_rows']}
success={r['module']:r for r in live['records'] if r['exit_code']==0};rows=[];new=[]
archive2=HERE/'data/case7302-successful-log-snapshot.zip'
with zipfile.ZipFile(archive2,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as out:
    for name,r in success.items():
        p=CASE/'logs'/(name.replace('/','-')+'.log');raw=p.read_bytes();lh=hashlib.sha256(raw).hexdigest()
        assert 'error:' not in raw.decode() and 'sorryAx' not in raw.decode()
        if name in prior:
            assert prior[name]['source_sha256']==r['source_sha256'] and prior[name]['log_sha256']==lh
            oh=prior[name]['object_sha256'];scope='Inherited from pinned milestone92 checkpoint'
        else:
            assert sha(CASE/'lean'/(name+'.lean'))==r['source_sha256']
            oh=sha(Path(live['build'])/(name+'.olean'));new.append(name);scope='Source and object rehashed at milestone93'
        info=zipfile.ZipInfo(p.name,(1980,1,1,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;out.writestr(info,raw)
        rows.append(dict(module=name,source_sha256=r['source_sha256'],object_sha256=oh,object_hash_scope=scope,
                         log_sha256=lh,log_archive_member=p.name))
assert set(prior)<=set(success)
(HERE/'logs/case7302-Check1-timeout.log').write_bytes((CASE/'logs/LocalWindowUnsat-ShareWindow7302-Check1.log').read_bytes())
(HERE/'data/case7302-Check1-timeout-source.lean.txt').write_bytes((CASE/'lean/LocalWindowUnsat/ShareWindow7302/Check1.lean').read_bytes())

paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==old['paper_sha256']
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and ($_.CommandLine -like '*case7302*' -or $_.CommandLine -like '*89-shared-cover-certification*' -or $_.CommandLine -like '*92-full-witness-batch*') } | Select-Object ProcessId,ParentProcessId,Name,CommandLine,PrivatePageCount) | ConvertTo-Json -Compress"
output=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(output) if output else []
if isinstance(processes,dict):processes=[processes]
assert not any('Check1.fresh-89-1793625531541364100.olean' in r['CommandLine'] for r in processes)
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
checkpoint=dict(status='PASS_FIXED_MODEL_COMPARISON_CERTIFICATES',previous_goal_turn='progress',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),new_lean_theorem_audits=7,
    comparison_receipt_sha256=sha(auditpath),independent_review_sha256=sha(HERE/'data/range-certificate-review.json'),
    checked_witness_classes=observations['witness']['classes'],observed_geometry_classes=observations['geometry']['classes'],
    new_witness_audits=observations['witness']['new_audits'],new_geometry_audits=observations['geometry']['new_audits'],
    batch_delta_sha256=sha(archive),run_observations=run_observations,process_observations=processes,
    witness_batch_tool_session=13482,geometric_batch_tool_session=23168,replay_tool_session=None,
    case7302_complete=False,case7302_replay_state='STOPPED_AFTER_CHECK1_TIMEOUT_900_SECONDS',
    case7302_confirmed_orphan_stopped=True,case7302_successful_rows=rows,case7302_distinct_successful_modules=len(rows),
    case7302_new_successful_modules=new,case7302_failed_attempts=[r for r in live['records'] if r['exit_code']!=0],
    case7302_successful_logs_sha256=sha(archive2),prior_checkpoint=oldpath.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(oldpath),
    unconditional_edge_interval=[191,235],conditional_target=234,pending_target_cases=[7301,7302,7303,7307,7308],
    upper_bound_evidence='Inspected contributor theorem and saved audit; full independent rebuild pending.',
    paper_revision=86,next_scheduled_paper_revision=96,paper_sha256=sha(paper),git_refs_before_commit=refs,
    next_task='Prove the exact key-dependent five-centre credit bound, prioritizing complete compatible variants for the 55 history share rules. Continue existing witness and geometry batches. Test an isolated case7302 segment before changing or restarting the six-segment timeout source.',
    scope='Seven new Lean comparison audits and independently checked finite-model witnesses. No new numerical snake bound; graph embedding, complete defined-graph potential and weight semantics remain separate.')
reproduction=HERE/'data/review-reproduction-audit.json'
if reproduction.exists():
    rr=read(reproduction)
    assert rr['status']=='PASS_SAVED_REVIEW_REPRODUCTION' and rr['all_fields_equal_except_timestamp']
    checkpoint['saved_review_reproduction_audit_sha256']=sha(reproduction)
save('checkpoint.json',checkpoint)
print('PASS_FIXED_MODEL_COMPARISON_CERTIFICATES;7 new Lean audits;',len(observations['witness']['classes']),'witness classes;',
      len(observations['geometry']['classes']),'geometry classes;',len(rows),'successful case7302 modules')
