"""Freeze checked history-share classification and continuing batch observations."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,time,zipfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
PREV=HERE.parent/'93-defined-graph-potential';WIT=HERE.parent/'92-full-witness-batch';GEO=HERE.parent/'89-shared-cover-certification'
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
def save(name,obj):(HERE/'data'/name).write_text(json.dumps(obj,indent=2)+'\n')

modules=[]
expected=['HistoryShareCover']+[f'ShareCover{i:02}' for i in range(11)]+['HistoryShareAssembly','HistoryShareCaps','HistoryShareValidity','HistoryShareCounts']
for name in expected:
    receipt=HERE/'data'/(name+'-audit.json');r=read(receipt);src=HERE/'lean'/(name+'.lean')
    assert r['status']=='PASS_HISTORY_SHARE_MODULE' and r['exit_code']==0
    assert sha(src)==r['source_sha256'] and sha(HERE/'build'/(name+'.olean'))==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    assert sha(HERE/'scripts/check.py')==r['checker_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
    assert src.read_text().count('#print axioms')==len(r['theorem_audits'])
    for row in r['theorem_audits']:assert set(row['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for dep,digest in r['dependencies'].items():assert sha(ROOT/dep)==digest
    modules.append(dict(module=name,receipt=receipt.relative_to(ROOT).as_posix(),receipt_sha256=sha(receipt),theorem_audits=len(r['theorem_audits'])))
assert sum(r['theorem_audits'] for r in modules)==73
v=read(HERE/'data/variants.json');g=read(HERE/'data/cover-generation.json')
assert v['status']=='PASS_COMPLETE_HISTORY_SHARE_VARIANTS_PYTHON'
assert sha(HERE/'scripts/prepare.py')==v['script_sha256']==g['script_sha256']
for path,digest in v['inputs'].items():assert sha(ROOT/path)==digest
assert sha(HERE/'data/variants.json')==g['variants_sha256']
for r in g['sources']:assert sha(HERE/'lean'/(r['module']+'.lean'))==r['source_sha256']
assert len(v['rows'])==55 and sum(len(r['variants']) for r in v['rows'])==69
assert sum(len(r['variants'])==1 for r in v['rows'])==41 and sum(len(r['variants'])==2 for r in v['rows'])==14
assert all(int(k)<6 and cap<6 for r in v['rows'] for k,cap in r['caps'].items())
assembly=(HERE/'lean/HistoryShareAssembly.lean').read_text()
pairs=re.findall(r'^  \(signature(\d{3}), variants(\d{3})\)',assembly,re.M)
assert pairs==[(f'{i:03}',f'{i:03}') for i in range(55)]
provenance=HERE/'data/credit-provenance.json';assert provenance.exists()
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
for p in [WIT/'data/witness-batch-active.json',*sorted((WIT/'logs').glob('witness-batch-run-*.json')),*sorted((GEO/'logs').glob('balanced-cover-run-*.json'))]:
    raw,r=stable(p);target=HERE/'data'/('snapshot-'+p.name);target.write_bytes(raw)
    runobs.append(dict(original=p.relative_to(ROOT).as_posix(),snapshot=target.name,sha256=sha(target),status=r.get('status'),active=r.get('active'),pid=r.get('pid')))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert sha(case/'logs/completion-record.json')==sha(PREV/'data/case7302-completion-observation.json')
assert not (case/'data/proof-audit.json').exists()
paper=ROOT/'paper/snake9_research.tex';assert sha(paper)==old['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and ($_.CommandLine -like '*case7302*' -or $_.CommandLine -like '*89-shared-cover-certification*' -or $_.CommandLine -like '*92-full-witness-batch*') } | Select-Object ProcessId,ParentProcessId,Name,CommandLine,PrivatePageCount) | ConvertTo-Json -Compress"
raw=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip();processes=json.loads(raw) if raw else []
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
summary=dict(status='PASS_COMPLETE_HISTORY_SHARE_CLASSIFICATION',theorem_audits=73,modules=modules,share_rules=55,variant_occurrences=69,singleton_signatures=41,doubleton_signatures=14,
             exact_local_compatible_sets_checked=True,actual_emission_transport_checked=True,numeric_caps_below_six_checked=True,
             concrete_geometric_credit_instances_checked=False,credit_provenance_sha256=sha(provenance),
             scope='All55 history-share compatible sets and actual-window/cap dispatch. Concrete per-word share bounds remain explicit premises; no new global bound.')
save('proof-summary.json',summary)
checkpoint=dict(status=summary['status'],previous_goal_turn='progress',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),new_lean_theorem_audits=73,
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),checked_witness_classes=observations['witness']['classes'],observed_geometry_classes=observations['geometry']['classes'],
    new_witness_audits=observations['witness']['new_audits'],new_geometry_audits=observations['geometry']['new_audits'],batch_delta_sha256=sha(archive),run_observations=runobs,process_observations=processes,
    witness_batch_tool_session=13482,geometric_batch_tool_session=23168,replay_tool_session=None,case7302_complete=False,
    case7302_replay_state='STOPPED_AFTER_CHECK1_TIMEOUT_900_SECONDS',case7302_distinct_successful_modules=old['case7302_distinct_successful_modules'],
    case7302_source_record_unchanged=True,prior_checkpoint=oldpath.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(oldpath),
    unconditional_edge_interval=[191,235],conditional_target=234,pending_target_cases=[7301,7302,7303,7307,7308],
    upper_bound_evidence='Inspected contributor theorem and saved audit; full independent rebuild pending.',paper_revision=86,next_scheduled_paper_revision=96,paper_sha256=sha(paper),git_refs_before_commit=refs,
    next_task='Port the existing local share support to the current share definition without namespace collisions; check a concrete credit instance and then instantiate all compatible-word bounds. Combine applicable history credits by maximum. Continue witness/geometry batches; retain case7302 timeout until a controlled isolated replay test.',scope=summary['scope'])
save('checkpoint.json',checkpoint)
print(summary['status'],'73 audits;',len(observations['witness']['classes']),'witness classes;',len(observations['geometry']['classes']),'geometry classes')
