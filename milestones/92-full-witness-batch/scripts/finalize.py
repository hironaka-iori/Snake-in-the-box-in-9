"""Freeze completed context assignment and the current full witness-batch state."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, time, zipfile
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PREV = HERE.parent / '91-reference-shape-reuse'
SUPPORT = HERE.parent / '90-context-witness-certificates'
GEOMETRY = HERE.parent / '89-shared-cover-certification'
OLD = HERE.parent / '88-retention-diagram-certificate'
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b''):
            h.update(chunk)
    return h.hexdigest()

def stable(p):
    for attempt in range(10):
        raw = p.read_bytes()
        try:
            return raw, json.loads(raw)
        except json.JSONDecodeError:
            if attempt == 9: raise
            time.sleep(.1)

def check_module(base, path, trial=False):
    r = read(path); name = r['module']
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    source = base / 'lean' / (name+'.lean')
    log = ROOT / r['immutable_trial_log'] if trial else base / 'logs' / (name+'.log')
    assert sha(source) == r['source_sha256']
    assert sha(base / 'build' / (name+'.olean')) == r['olean_sha256']
    assert sha(log) == r['log_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text())
    assert len(r['theorem_audits']) == source.read_text().count('#print axioms')
    for row in r['theorem_audits']:
        assert set(row['axioms']) <= {'propext','Classical.choice','Quot.sound'}
    for dep,digest in r.get('dependencies',r.get('dependency_receipts',{})).items():
        paths = [ROOT / dep] if dep.startswith('milestones') else [b/'data'/(dep+'-audit.json') for b in [HERE,PREV,SUPPORT,GEOMETRY,OLD]]
        assert any(p.exists() and sha(p)==digest for p in paths), (name,dep)
    return dict(module=name,receipt=path.relative_to(ROOT).as_posix(),receipt_sha256=sha(path),
                theorem_audits=len(r['theorem_audits']),seconds=r['seconds'])

modules=[]
for p in sorted((HERE/'data').glob('*-audit.json')):
    r=read(p)
    if 'module' in r and p.name==r['module']+'-audit.json':modules.append(check_module(HERE,p))
module_names={r['module'] for r in modules}
assert {'BatchAssembly','BatchContextData','ContextAssignmentData','ContextAssignment','ContextAssignmentChecks'}<=module_names
classes=sorted(int(m.group(1)) for name in module_names if (m:=re.fullmatch(r'Witness(\d{3})Checks',name)))
assert {0,1,2}<=set(classes)
generation=read(HERE/'data/batch-generation.json')
assert sha(HERE/'scripts/build_batch.py')==generation['script_sha256']
for path,digest in generation['input_sha256'].items():assert sha(ROOT/path)==digest,path
for name,digest in generation['source_sha256'].items():assert sha(HERE/'lean'/name)==digest,name
closure=read(HERE/'data/closure-generation.json')
assert sha(HERE/'scripts/build_closure.py')==closure['script_sha256']
assert sha(HERE/'lean/CloseBatch.lean')==closure['source_sha256']
for path,digest in closure['input_sha256'].items():assert sha(ROOT/path)==digest,path
assignment=read(HERE/'data/ContextAssignment-build.json')
assert sha(HERE/'lean/ContextAssignmentData.lean')==assignment['source_sha256']
assert sha(HERE/'lean/BatchContextData.lean')==assignment['batch_context_source_sha256']
for path,digest in assignment['input_sha256'].items():assert sha(ROOT/path)==digest,path
lite=read(HERE/'data/ContextAssignmentLite-build.json')
assert sha(HERE/'lean/ContextAssignmentLiteData.lean')==lite['source_sha256']
assert sha(HERE/'data/ContextAssignment-build.json')==lite['original_build_sha256']
assert sha(HERE/'lean/BatchContextData.lean')==lite['batch_context_source_sha256']
assert sha(HERE/'data/context-assignment-plan.json')==lite['plan_sha256']
chunk_data=read(HERE/'data/ContextAssignmentLite-chunks.json')
assert sha(HERE/'lean/ContextAssignmentLiteChecks.lean')==chunk_data['assembly_source_sha256']
assert sha(HERE/'data/ContextAssignmentLite-build.json')==chunk_data['lite_build_sha256']
assert len(chunk_data['chunks'])==26
assert sum(r['count'] for r in chunk_data['chunks'])==505
assert sum(r['positions'] for r in chunk_data['chunks'])==37875
assert sum(r['compatible_contexts'] for r in chunk_data['chunks'])==791
for i,r in enumerate(chunk_data['chunks']):
    assert r['index']==i and r['start']==20*i and r['count']==min(20,505-20*i)
    assert sha(HERE/'lean'/(r['module']+'.lean'))==r['source_sha256']
    assert r['module'] in module_names
timeout=read(HERE/'data/ContextAssignmentChecks-timeout.json')
assert timeout['status']=='TIMEOUT_CHILD_TERMINATED' and timeout['child_stopped']
for artifact in ['source','log','checker']:assert sha(Path(timeout[artifact+'_snapshot']))==timeout[artifact+'_sha256']
versions=read(HERE/'data/checker-revisions.json')['revisions']
for r in versions:assert sha(HERE/r['path'])==r['sha256']
checker_hashes={r['sha256'] for r in versions}
own_runs=[]
for p in sorted((HERE/'logs').glob('witness-batch-run-*.json')):
    raw,r=stable(p)
    assert r['checker_sha256'] in checker_hashes
    target=HERE/'data'/('snapshot-'+p.name);target.write_bytes(raw)
    own_runs.append(dict(original=p.relative_to(ROOT).as_posix(),snapshot=target.name,sha256=sha(target),
                         status=r['status'],active=r.get('active'),pid=r['pid'],waiting_class=r.get('waiting_class'),memory_wait=r.get('memory_wait')))
assert any(r['status'] in ['RUNNING','WAITING_FOR_GEOMETRY','WAITING_FOR_MEMORY','PASS_ALL_CLASSES_AND_NUMERIC_DIAGRAM'] for r in own_runs)
old_checkpoint=PREV/'data/checkpoint.json';old=read(old_checkpoint)
prior_geometry={r['module'] for r in read(PREV/'data/geometry-observation.json')['modules']}
geometry_modules,geometry_classes,geometry_paths=[],[],[]
for p in sorted((GEOMETRY/'data').glob('*-audit.json')):
    if re.fullmatch(r'(?:Balanced\d{3}|Cover\d{3})(?:Data|Checks)-audit.json',p.name):
        r=check_module(GEOMETRY,p);geometry_modules.append(r)
        match=re.fullmatch(r'Balanced(\d{3})Checks',r['module'])
        if match:geometry_classes.append(int(match[1]))
        if r['module'] not in prior_geometry:
            geometry_paths += [p,GEOMETRY/'logs'/(r['module']+'.log'),GEOMETRY/'logs'/(r['module']+'-record.json')]
geometry=dict(status='OBSERVED_SUCCESSFUL_GEOMETRY_MODULES',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),classes=sorted(geometry_classes),modules=geometry_modules,
    new_theorem_audits=sum(r['theorem_audits'] for r in geometry_modules if r['module'] not in prior_geometry),
    archive_paths=[p.relative_to(ROOT).as_posix() for p in geometry_paths],
    scope='Immutable successful receipts at this snapshot; the existing sequential geometry batch continues.')
(HERE/'data/geometry-observation.json').write_text(json.dumps(geometry,indent=2)+'\n')
external_runs=[]
for p in [*sorted((GEOMETRY/'logs').glob('balanced-cover-run-*.json')),GEOMETRY/'logs/case7302-unique-resume-run.json']:
    raw,r=stable(p);target=HERE/'data'/('snapshot-'+p.name);target.write_bytes(raw)
    external_runs.append(dict(original=p.relative_to(ROOT).as_posix(),snapshot=target.name,sha256=sha(target),
                              status=r['status'],active=r.get('active')))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists(),'Case completed: refresh local-share status'
raw,live=stable(case/'logs/completion-record.json');(HERE/'data/case7302-completion-observation.json').write_bytes(raw)
success={r['module']:r for r in live['records'] if r['exit_code']==0};prior={r['module']:r for r in old['case7302_successful_rows']}
rows,new_rows=[],[];archive=HERE/'data/case7302-successful-log-snapshot.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as out:
    for name,row in success.items():
        log=case/'logs'/(name.replace('/','-')+'.log');raw=log.read_bytes();loghash=hashlib.sha256(raw).hexdigest()
        assert 'error:' not in raw.decode() and 'sorryAx' not in raw.decode()
        if name in prior:
            assert prior[name]['source_sha256']==row['source_sha256'] and prior[name]['log_sha256']==loghash
            objecthash=prior[name]['object_sha256'];scope='Inherited object hash from pinned milestone91; not rehashed in this delta'
        else:
            assert sha(case/'lean'/(name+'.lean'))==row['source_sha256']
            objecthash=sha(Path(live['build'])/(name+'.olean'));new_rows.append(name);scope='Source and object bytes hashed in milestone92'
        info=zipfile.ZipInfo(log.name,(1980,1,1,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;out.writestr(info,raw)
        rows.append(dict(module=name,source_sha256=row['source_sha256'],object_sha256=objecthash,
                         object_hash_scope=scope,log_sha256=loghash,log_archive_member=log.name))
assert set(prior)<=set(success)
with zipfile.ZipFile(archive) as saved:
    for r in rows:assert hashlib.sha256(saved.read(r['log_archive_member'])).hexdigest()==r['log_sha256']
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==old['paper_sha256']
completed=[generation['classes'][i] for i in classes]
full='CloseBatch' in module_names
assert not full or len(classes)==127
status='PASS_ALL_CLASSES_AND_NUMERIC_DIAGRAM' if full else 'PASS_CONTEXT_ASSIGNMENT_PARTIAL_WITNESS_BATCH'
summary=dict(status=status,theorem_audits=sum(r['theorem_audits'] for r in modules),modules=modules,
    checked_witness_classes=classes,total_classes=127,checked_contexts=sum(r['contexts'] for r in completed),total_contexts=791,
    checked_base_jobs=sum(r['base_jobs'] for r in completed),total_base_jobs=507,
    checked_history_heads=sum(r['history_heads'] for r in completed),total_history_heads=3,reused_class1_jobs=6,
    context_assignment_checked=True,assignment_positions=37875,count_codes_enumerated_for_assignment=0,
    exact_saved_class_and_root_coherence=True,full_numeric_diagram_checked=full,
    defined_graph_bridge_checked='DefinedProofGraph' in module_names,
    queued_closure_sha256=closure['source_sha256'],observed_geometry_classes=sorted(geometry_classes),
    newly_observed_geometry_audits=geometry['new_theorem_audits'],
    reference_premises=['AllRefuted6K235','AllRefuted236'],
    remaining=['Finish uncompleted class receipts and final family assembly','Instantiate the graph defined from accepted full keys',
               'Check weights and potentials on that defined graph','Reference catalogue closure','Pending local shares and credit interpretation'],
    scope='Source-compatible context assignment and exact saved class/root selection checked. The listed concrete witness classes are checked. The full family requires all127 receipts and CloseBatch; no new numerical bound.')
(HERE/'data/proof-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and ($_.CommandLine -like '*case7302*' -or $_.CommandLine -like '*89-shared-cover-certification*' -or $_.CommandLine -like '*92-full-witness-batch*') } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
raw=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip();processes=json.loads(raw) if raw else []
if isinstance(processes,dict):processes=[processes]
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
active=read(HERE/'data/witness-batch-active.json')
checkpoint=dict(status=status,recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),theorem_audits=summary['theorem_audits'],
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),checked_witness_classes=classes,
    observed_geometry_classes=sorted(geometry_classes),witness_run_observations=own_runs,external_run_observations=external_runs,
    witness_batch_active_record=active,witness_batch_tool_session=read(HERE/'data/witness-launch.json')['tool_session'],
    geometric_batch_tool_session=23168,replay_tool_session=14427,
    authoritative_process_observations=processes,case7302_complete=False,case7302_successful_rows=rows,
    case7302_distinct_successful_modules=len(rows),case7302_new_successful_modules=new_rows,
    case7302_raw_successful_record_count=sum(r['exit_code']==0 for r in live['records']),
    case7302_failed_attempts=[r for r in live['records'] if r['exit_code']!=0],case7302_successful_logs_sha256=sha(archive),
    case7302_prior_checkpoint=old_checkpoint.relative_to(ROOT).as_posix(),case7302_prior_checkpoint_sha256=sha(old_checkpoint),
    unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence='Inspected contributor theorem and saved audit; no complete independent rebuild.',
    pending_target_cases=[7301,7302,7303,7307,7308],paper_revision=86,next_scheduled_paper_revision=96,
    paper_sha256=sha(paper),git_refs_before_commit=refs,
    next_task='Continue the existing sequential witness and geometry batches and case7302 replay without duplicates. The context selector is checked. Use the graph defined from diagram-accepted keys with endpoints computed from keys; check all weights and potentials on that graph. Keep reference and pending local-share premises explicit.')
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(status,summary['theorem_audits'],'audits;',len(classes),'witness classes;',len(geometry_classes),'geometry classes;',len(rows),'replay modules')

