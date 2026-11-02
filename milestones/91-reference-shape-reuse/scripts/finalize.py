"""Verify the completed cache experiment and freeze continuing proof observations."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, time, zipfile
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PREV = HERE.parent / '90-context-witness-certificates'
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
        paths = [ROOT / dep] if dep.startswith('milestones') else [b/'data'/(dep+'-audit.json') for b in [HERE,PREV,GEOMETRY,OLD]]
        assert any(p.exists() and sha(p)==digest for p in paths), (name,dep)
    return dict(module=name,receipt=path.relative_to(ROOT).as_posix(),receipt_sha256=sha(path),
                theorem_audits=len(r['theorem_audits']),seconds=r['seconds'])

modules = [check_module(HERE,HERE/'data'/(name+'-audit.json')) for name in
           ['ShapeCache','CachePilotData','CachePilotChecks','DirectPilotChecks']]
assert sum(r['theorem_audits'] for r in modules if r['module']!='DirectPilotChecks') == 8
generation = read(HERE/'data/pilot-generation.json')
assert sha(HERE/'scripts/build_pilot.py') == generation['script_sha256']
for path,digest in generation['input_sha256'].items(): assert sha(ROOT/path) == digest
for name,digest in generation['source_sha256'].items(): assert sha(HERE/'lean'/name) == digest
assert sha(HERE/'data/cache-pilot.json.gz') == generation['payload_sha256']
assert (HERE/'lean/DirectPilotChecks.lean').read_bytes() == (PREV/'lean/Class001WitnessChecks.lean').read_bytes()
trials = []
for p in sorted((HERE/'data').glob('*-trial-*-audit.json')):
    r = check_module(HERE,p,True); data = read(p)
    r['trial'] = data['trial']
    r['other_lean_processes_before'] = sum(x['Name'].lower()=='lean.exe' for x in data['processes_before'])
    r['new_theorems'] = 0
    trials.append(r)
trials.sort(key=lambda r:r['trial'])
proof_trials = [r for r in trials if r['module']!='CachePilotData']
assert [r['module'] for r in proof_trials] == ['DirectPilotChecks','CachePilotChecks','CachePilotChecks','DirectPilotChecks']
assert all(r['other_lean_processes_before']==2 for r in trials)
for p in (HERE/'logs').glob('pilot-run-*.json'):
    r = read(p)
    assert r['status']=='PASS_SELECTED_SHAPE_PILOT_TRIALS' and 'active' not in r
    assert sha(HERE/'scripts/check_pilot.py') == r['checker_sha256']
benchmark = dict(status='PASS_SAME_CONCLUSION_COMPARISON_NO_ESTABLISHED_SPEEDUP', trials=trials,
    direct_seconds=[r['seconds'] for r in proof_trials if r['module']=='DirectPilotChecks'],
    cached_seconds=[r['seconds'] for r in proof_trials if r['module']=='CachePilotChecks'],
    generic_setup_seconds=read(HERE/'data/ShapeCache-audit.json')['seconds'],
    cache_data_seconds=read(HERE/'data/CachePilotData-audit.json')['seconds'],
    direct_source_byte_identical=True,repeated_objects_byte_identical=True,
    proof_scope='Cached proof includes all finite shape, count, descriptor, guard, length and assembly checks.',
    limits='Two trials per method, two other active Lean workloads, no isolation or controlled load. Generation and shared old dependencies excluded.',
    decision='Use direct balanced-lookup checker for the full witness batch. Cache is sound; no consistent performance advantage established.')
(HERE/'data/benchmark-summary.json').write_text(json.dumps(benchmark,indent=2)+'\n')

old_checkpoint = PREV/'data/checkpoint.json'; old = read(old_checkpoint)
prior_geometry = {r['module'] for r in read(PREV/'data/geometry-observation.json')['modules']}
geometry_modules,classes,archive_paths = [],[],[]
for path in sorted((GEOMETRY/'data').glob('*-audit.json')):
    if re.fullmatch(r'(?:Balanced\d{3}|Cover\d{3})(?:Data|Checks)-audit.json',path.name):
        r = check_module(GEOMETRY,path); geometry_modules.append(r)
        match = re.fullmatch(r'Balanced(\d{3})Checks',r['module'])
        if match: classes.append(int(match[1]))
        if r['module'] not in prior_geometry:
            archive_paths += [path,GEOMETRY/'logs'/(r['module']+'.log'),GEOMETRY/'logs'/(r['module']+'-record.json')]
geometry = dict(status='OBSERVED_SUCCESSFUL_GEOMETRY_MODULES',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),classes=sorted(classes),modules=geometry_modules,
    new_theorem_audits=sum(r['theorem_audits'] for r in geometry_modules if r['module'] not in prior_geometry),
    archive_paths=[p.relative_to(ROOT).as_posix() for p in archive_paths],
    scope='Immutable successful receipts at this snapshot; the existing sequential batch continues.')
(HERE/'data/geometry-observation.json').write_text(json.dumps(geometry,indent=2)+'\n')
run_snapshots = []
for p in [*sorted((GEOMETRY/'logs').glob('balanced-cover-run-*.json')),GEOMETRY/'logs/case7302-unique-resume-run.json']:
    raw,r = stable(p); target = HERE/'data'/('snapshot-'+p.name); target.write_bytes(raw)
    run_snapshots.append(dict(original=p.relative_to(ROOT).as_posix(),snapshot=target.name,sha256=sha(target),
                              status=r['status'],active=r.get('active')))
case = ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists(), 'Final case audit appeared: refresh completed status'
raw,live = stable(case/'logs/completion-record.json')
(HERE/'data/case7302-completion-observation.json').write_bytes(raw)
success = {r['module']:r for r in live['records'] if r['exit_code']==0}
prior = {r['module']:r for r in old['case7302_successful_rows']}
rows,new_rows = [],[]; archive = HERE/'data/case7302-successful-log-snapshot.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as out:
    for name,row in success.items():
        log = case/'logs'/(name.replace('/','-')+'.log'); raw = log.read_bytes()
        loghash = hashlib.sha256(raw).hexdigest()
        assert 'error:' not in raw.decode() and 'sorryAx' not in raw.decode()
        if name in prior:
            assert prior[name]['source_sha256']==row['source_sha256'] and prior[name]['log_sha256']==loghash
            objecthash = prior[name]['object_sha256']
            scope = 'Inherited object hash from pinned milestone90; object not rehashed in this delta'
        else:
            assert sha(case/'lean'/(name+'.lean'))==row['source_sha256']
            objecthash = sha(Path(live['build'])/(name+'.olean')); new_rows.append(name)
            scope = 'Source and object bytes hashed in milestone91'
        info = zipfile.ZipInfo(log.name,(1980,1,1,0,0,0)); info.compress_type = zipfile.ZIP_DEFLATED
        out.writestr(info,raw)
        rows.append(dict(module=name,source_sha256=row['source_sha256'],object_sha256=objecthash,
                         object_hash_scope=scope,log_sha256=loghash,log_archive_member=log.name))
assert set(prior)<=set(success)
with zipfile.ZipFile(archive) as saved:
    for row in rows: assert hashlib.sha256(saved.read(row['log_archive_member'])).hexdigest()==row['log_sha256']
paper = ROOT/'paper/snake9_research.tex'
assert sha(paper)==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==old['paper_sha256']
summary = dict(status='PASS_CERTIFIED_SHAPE_REUSE_WITH_INCONCLUSIVE_TIMING',theorem_audits=8,
    distinct_checked_theorems_including_baseline=10,rechecked_baseline_theorems=2,modules=modules,
    generic_new_audits=3,concrete_new_audits=5,concrete_class=1,directions=[1,3,307,308,310,312],
    entries=3840,reference_entries=3732,certified_shapes=156,nonreference_fallbacks=108,count_lists=2,
    all_contexts_checked=False,new_numerical_bound=False,benchmark_summary_sha256=sha(HERE/'data/benchmark-summary.json'),
    observed_geometry_classes=sorted(classes),new_geometry_audits=geometry['new_theorem_audits'],
    next_method='Direct balanced-lookup witness certification',reference_premises=['AllRefuted6K235','AllRefuted236'],
    scope='Generic certified shape substitution and complete six-direction cache pilot checked. Direct comparison repeats prior theorems. No full finite coverage, graph interpretation or improved bound.')
(HERE/'data/proof-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
command = "@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and ($_.CommandLine -like '*case7302*' -or $_.CommandLine -like '*89-shared-cover-certification*') } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
raw = subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes = json.loads(raw) if raw else []
if isinstance(processes,dict): processes=[processes]
refs = {ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
checkpoint = dict(status=summary['status'],recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    theorem_audits=8,proof_summary_sha256=sha(HERE/'data/proof-summary.json'),observed_geometry_classes=sorted(classes),
    run_observations=run_snapshots,geometric_batch_tool_session=23168,replay_tool_session=14427,
    completed_pilot_tool_session=70247,authoritative_process_observations=processes,case7302_complete=False,
    case7302_successful_rows=rows,case7302_distinct_successful_modules=len(rows),case7302_new_successful_modules=new_rows,
    case7302_raw_successful_record_count=sum(r['exit_code']==0 for r in live['records']),
    case7302_failed_attempts=[r for r in live['records'] if r['exit_code']!=0],case7302_successful_logs_sha256=sha(archive),
    case7302_prior_checkpoint=old_checkpoint.relative_to(ROOT).as_posix(),case7302_prior_checkpoint_sha256=sha(old_checkpoint),
    unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence='Inspected contributor theorem and saved audit; no complete independent rebuild.',
    pending_target_cases=[7301,7302,7303,7307,7308],paper_revision=86,next_scheduled_paper_revision=96,
    paper_sha256=sha(paper),git_refs_before_commit=refs,
    next_task='Expand the direct checker to the saved 507 base jobs and three history heads, with complete context assignment. Do not repeat the cache benchmark without a materially changed representation. Continue both existing proof runs.')
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(summary['status'],'8 new audits;',len(classes),'geometry classes;',len(rows),'distinct replay modules')
