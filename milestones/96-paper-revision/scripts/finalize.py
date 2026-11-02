"""Freeze paper revision96 and inherited batch evidence without restarting jobs."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys,time,zipfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
PREV=HERE.parent/'95-history-credit-integration';WIT=HERE.parent/'92-full-witness-batch';GEO=HERE.parent/'89-shared-cover-certification'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,obj):(HERE/'data'/name).write_text(json.dumps(obj,indent=2)+'\n')
def stable(p):
    for i in range(10):
        raw=p.read_bytes()
        try:return raw,json.loads(raw)
        except json.JSONDecodeError:
            if i==9:raise
            time.sleep(.1)

oldpath=PREV/'data/checkpoint.json';old=read(oldpath)
prior=read(PREV/'data/batch-progress-observation.json');observations={}
archive=HERE/'data/completed-batch-delta.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as out:
    for label,base,pattern,prefix in [('geometry',GEO,r'(?:Balanced\d{3}|Cover\d{3})(?:Data|Checks)-audit.json','Balanced'),('witness',WIT,r'Witness\d{3}(?:Data|Checks)-audit.json','Witness')]:
        oldrows={r['module']:r for r in prior[label]['modules']};rows=[];new=[]
        for receipt in sorted((base/'data').glob('*-audit.json')):
            if not re.fullmatch(pattern,receipt.name):continue
            name=receipt.name.removesuffix('-audit.json')
            if name in oldrows:
                assert sha(receipt)==oldrows[name]['receipt_sha256'];row=oldrows[name]
            else:
                raw,r=stable(receipt);src=base/'lean'/(name+'.lean');log=base/'logs'/(name+'.log')
                assert r['exit_code']==0 and r['status'].startswith('PASS_')
                assert sha(src)==r['source_sha256'] and sha(base/'build'/(name+'.olean'))==r['olean_sha256'] and sha(log)==r['log_sha256']
                assert src.read_text().count('#print axioms')==len(r['theorem_audits'])
                for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
                row=dict(module=name,receipt=receipt.relative_to(ROOT).as_posix(),receipt_sha256=sha(receipt),theorem_audits=len(r['theorem_audits']),source_sha256=r['source_sha256'],object_sha256=r['olean_sha256'],log_sha256=r['log_sha256'])
                new.append(name)
                for p in [receipt,log,base/'logs'/(name+'-record.json')]:
                    if p.exists():
                        info=zipfile.ZipInfo(p.relative_to(ROOT).as_posix(),(1980,1,1,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;out.writestr(info,p.read_bytes())
            rows.append(row)
        classes=sorted(int(m.group(1)) for r in rows if (m:=re.fullmatch(prefix+r'(\d{3})Checks',r['module'])))
        observations[label]=dict(classes=classes,modules=rows,new_modules=new,new_audits=sum(r['theorem_audits'] for r in rows if r['module'] in new))
save('batch-progress-observation.json',observations)
runobs=[]
for p in [WIT/'data/witness-batch-active.json',GEO/'data/balanced-cover-active.json',*sorted((WIT/'logs').glob('witness-batch-run-*.json')),*sorted((GEO/'logs').glob('balanced-cover-run-*.json'))]:
    if not p.exists():continue
    raw,r=stable(p);target=HERE/'data'/('snapshot-'+p.name);target.write_bytes(raw)
    runobs.append(dict(original=p.relative_to(ROOT).as_posix(),snapshot=target.name,sha256=sha(target),status=r.get('status'),active=r.get('active'),pid=r.get('pid')))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert sha(case/'logs/completion-record.json')==sha(ROOT/'milestones/93-defined-graph-potential/data/case7302-completion-observation.json')
assert not (case/'data/proof-audit.json').exists()
paper=ROOT/'paper/snake9_research.tex'; verification=read(HERE/'data/verification.json')
assert verification['status']=='PASS_PAPER96_SOURCE_AND_MATHEMATICAL_DATA'
assert sha(paper)==verification['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
compiler=read(HERE/'data/compiler-result.json');assert compiler['status']=='PREVIEW_UNAVAILABLE_BEFORE_SOURCE_COMPILATION'
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main'],'Remote changed: inspect before integration'
c=dict(status='PASS_PAPER96_SOURCE_REVISION_PREVIEW_UNAVAILABLE',previous_goal_turn='progress',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    verification_sha256=sha(HERE/'data/verification.json'),compiler_result_sha256=sha(HERE/'data/compiler-result.json'),new_lean_theorem_audits=0,
    checked_witness_classes=observations['witness']['classes'],observed_geometry_classes=observations['geometry']['classes'],new_witness_audits=observations['witness']['new_audits'],new_geometry_audits=observations['geometry']['new_audits'],batch_delta_sha256=sha(archive),run_observations=runobs,
    witness_batch_tool_session=13482,geometric_batch_tool_session=23168,replay_tool_session=None,case7302_complete=False,case7302_replay_state='STOPPED_AFTER_CHECK1_TIMEOUT_900_SECONDS',case7302_distinct_successful_modules=649,case7302_source_record_unchanged=True,
    prior_checkpoint=oldpath.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(oldpath),unconditional_edge_interval=[191,235],conditional_target=234,pending_target_cases=[7301,7302,7303,7307,7308],upper_bound_evidence=old['upper_bound_evidence'],
    paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=sha(paper),git_refs_before_commit=refs,
    next_task='Assemble the remaining graph-weight components with actual full-key equality, then check the complete potential on the defined graph. Continue existing witness and geometry batches and preserve the stopped case7302 replay.',
    scope='Four existing-result statements integrated, zero new named definitions, complete history table and exact source checks. No new numerical bound, new Lean theorem, successful PDF compilation or visual layout check.')
save('checkpoint.json',c)
print(c['status'],len(observations['witness']['classes']),'witness classes;',len(observations['geometry']['classes']),'geometry classes')
