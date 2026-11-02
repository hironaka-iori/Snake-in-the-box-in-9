"""Freeze the completed concrete history-credit integration and batch progress."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys,time,zipfile

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
PREV=HERE.parent/'94-history-share-dispatch';WIT=HERE.parent/'92-full-witness-batch';GEO=HERE.parent/'89-shared-cover-certification'
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

assert not (HERE/'data/check.lock').exists(),'A milestone95 checker is still active'
subprocess.run([sys.executable,'-X','utf8',str(HERE/'scripts/audit_sources.py')],check=True)
subprocess.run([sys.executable,'-X','utf8',str(HERE/'scripts/audit_credits.py')],check=True)
generation=read(HERE/'data/credit-generation.json')
for path,digest in generation['inputs'].items():assert sha(ROOT/path)==digest,path
for module,digest in generation['generated_sources'].items():assert sha(HERE/'lean'/(module+'.lean'))==digest,module
audit=read(HERE/'data/source-audit.json')
names={r['module'] for r in audit['modules']}
assert 'ConcreteRules95' in names
assert {p.stem for p in (HERE/'lean').glob('*.lean')}==names
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
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
summary=dict(status='PASS_COMPLETE_CONCRETE_HISTORY_CREDITS',modules=audit['modules'],theorem_audits=audit['theorem_audits'],share_rules=55,geometric_word_bounds=69,capped_word_bounds=8,ported_modules=46,
    concrete_geometric_credit_instances_checked=True,maximum_credit_evaluator_checked=True,combined_defined_graph_import_checked=True,
    source_audit_sha256=sha(HERE/'data/source-audit.json'),credit_literal_audit_sha256=sha(HERE/'data/credit-literal-audit.json'),credit_generation_sha256=sha(HERE/'data/credit-generation.json'),scope='The saved55 history rules bound the actual five-centre share sum. Remaining graph-weight components, retention premises and global potential are separate; no new numerical snake bound.')
save('proof-summary.json',summary)
c=dict(status=summary['status'],previous_goal_turn='progress',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),new_lean_theorem_audits=summary['theorem_audits'],
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),checked_witness_classes=observations['witness']['classes'],observed_geometry_classes=observations['geometry']['classes'],
    new_witness_audits=observations['witness']['new_audits'],new_geometry_audits=observations['geometry']['new_audits'],batch_delta_sha256=sha(archive),run_observations=runobs,
    witness_batch_tool_session=13482,geometric_batch_tool_session=23168,replay_tool_session=None,case7302_complete=False,
    case7302_replay_state='STOPPED_AFTER_CHECK1_TIMEOUT_900_SECONDS',case7302_distinct_successful_modules=649,case7302_source_record_unchanged=True,
    prior_checkpoint=oldpath.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(oldpath),unconditional_edge_interval=[191,235],conditional_target=234,
    pending_target_cases=[7301,7302,7303,7307,7308],upper_bound_evidence=old['upper_bound_evidence'],paper_revision=86,next_scheduled_paper_revision=96,paper_sha256=sha(paper),git_refs_before_commit=refs,
    next_task='Revise the existing paper at milestone96, then assemble the remaining graph-weight components and check the potential on the complete defined graph. Continue witness/geometry batches and preserve case7302 timeout evidence.',scope=summary['scope'])
save('checkpoint.json',c)
print(summary['status'],summary['theorem_audits'],'audits;',len(observations['witness']['classes']),'witness classes;',len(observations['geometry']['classes']),'geometry classes')
