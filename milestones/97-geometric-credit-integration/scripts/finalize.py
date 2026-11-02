"""Freeze completed geometric integration, sensitivity certificates and inherited jobs."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys,time,zipfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
PREV=HERE.parent/'96-paper-revision';WIT=HERE.parent/'92-full-witness-batch';GEO=HERE.parent/'89-shared-cover-certification'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,obj):(HERE/'data'/name).write_text(json.dumps(obj,indent=2)+'\n')
assert not (HERE/'data/check.lock').exists(),'The geometric checker is still active'
subprocess.run([sys.executable,'-X','utf8',str(HERE/'scripts/audit.py'),'--complete'],check=True)
summary=read(HERE/'data/proof-summary.json')
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
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==old['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
coverage=None
receipt=WIT/'data/CloseBatch-audit.json'
if receipt.exists():
    r=read(receipt);assert r['exit_code']==0 and r['status']=='PASS_NUMERIC_DIAGRAM_FAMILY'
    assert sha(WIT/'lean/CloseBatch.lean')==r['source_sha256'] and sha(WIT/'build/CloseBatch.olean')==r['olean_sha256'] and sha(WIT/'logs/CloseBatch.log')==r['log_sha256']
    for p,h in r['dependencies'].items():assert sha(ROOT/p)==h
    assert len(r['theorem_audits'])==3 and all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['theorem_audits'])
    coverage=dict(receipt=receipt.relative_to(ROOT).as_posix(),receipt_sha256=sha(receipt),scope='Complete numeric diagram coverage and actual walk under two reference-catalogue premises. Weights, potential and unfinished local shares remain separate.')
    (HERE/'data/CloseBatch-observation.json').write_bytes(receipt.read_bytes())
    with zipfile.ZipFile(archive,'a',compression=zipfile.ZIP_DEFLATED) as out:
        for p in [receipt,WIT/'logs/CloseBatch.log',WIT/'logs/CloseBatch-record.json']:
            if p.exists():out.writestr(p.relative_to(ROOT).as_posix(),p.read_bytes())
sensitivity=read(HERE/'floor-sensitivity/verification.json');assert sensitivity['status']=='PASS_INDEPENDENT_FINITE_GRAPH_CERTIFICATES'
minimum=read(HERE/'floor-sensitivity/012034-minimum/verification.json')
assert minimum['status']=='PASS_SHARP_FIXED_GRAPH_INTEGER_FLOOR_THRESHOLD'
assert minimum['least_feasible_integer_floor']==18 and minimum['adjacent_obstructed_floor']==17
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main'],'Remote changed: inspect before integration'
c=dict(status='PASS_GEOMETRIC_HISTORY_CREDIT_INTEGRATION',previous_goal_turn='progress',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),proof_summary_sha256=sha(HERE/'data/proof-summary.json'),new_lean_theorem_audits=summary['theorem_audits'],geometric_shapes=505,positive_geometric_shapes=357,geometric_and_history_maximum_checked=True,symbol_credit_transfers_checked=(HERE/'data/SymbolCredit97-audit.json').exists(),pressure_arithmetic_checked=(HERE/'data/PressureArithmetic97-audit.json').exists(),
    checked_witness_classes=observations['witness']['classes'],observed_geometry_classes=observations['geometry']['classes'],new_witness_audits=observations['witness']['new_audits'],new_geometry_audits=observations['geometry']['new_audits'],batch_delta_sha256=sha(archive),run_observations=runobs,complete_numeric_coverage=coverage,
    witness_batch_tool_session=13482,geometric_batch_tool_session=23168,replay_tool_session=None,geometric_credit_session=83238,geometric_credit_batch_complete=True,
    case7302_complete=False,case7302_replay_state='STOPPED_AFTER_CHECK1_TIMEOUT_900_SECONDS',case7302_distinct_successful_modules=649,case7302_source_record_unchanged=True,
    sensitivity_verification_sha256=sha(HERE/'floor-sensitivity/verification.json'),minimum_floor_verification_sha256=sha(HERE/'floor-sensitivity/012034-minimum/verification.json'),least_pending_floor_vector=[16,18,16,16,16],optimized_012034_floor=18,optimized_potential_mean=496,optimized_potential_range=602,optimized_strict_margin=30,prior_checkpoint=oldpath.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(oldpath),unconditional_edge_interval=[191,235],conditional_target=234,pending_target_cases=[7301,7302,7303,7307,7308],upper_bound_evidence=old['upper_bound_evidence'],paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=sha(paper),git_refs_before_commit=refs,
    next_task='Instantiate the count-conditioned credits and count-free profile in the common environment, using the sensitivity certificates to choose the least demanding valid 012034 target. Preserve the old replay. Check the complete potential on the same defined graph.',
    scope='All 505 geometric indices and the history-credit maximum for actual fitting windows; finite-graph floor sensitivity. No new universal share target or numerical global snake bound.')
save('checkpoint.json',c)
print(c['status'],summary['theorem_audits'],'audits;',len(observations['witness']['classes']),'witness classes;',len(observations['geometry']['classes']),'geometry classes')
