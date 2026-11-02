"""Freeze completed witness proofs and bounded observations of continuing jobs."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, time, zipfile

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PREV = HERE.parent / '89-shared-cover-certification'
OLD = HERE.parent / '88-retention-diagram-certificate'
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))


def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(part)
    return h.hexdigest()


def stable_read(p):
    for attempt in range(10):
        raw = p.read_bytes()
        try:
            return raw, json.loads(raw)
        except json.JSONDecodeError:
            if attempt == 9:
                raise
            time.sleep(.1)


def check_module(base, path):
    r = read(path)
    module = r['module']
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    source = base / 'lean' / (module + '.lean')
    assert sha(source) == r['source_sha256']
    assert sha(base / 'build' / (module + '.olean')) == r['olean_sha256']
    assert sha(base / 'logs' / (module + '.log')) == r['log_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b', source.read_text())
    assert len(r['theorem_audits']) == source.read_text().count('#print axioms')
    for row in r['theorem_audits']:
        assert set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    for name, digest in r.get('dependencies', r.get('dependency_receipts', {})).items():
        candidates = [ROOT / name] if name.startswith('milestones') else [
            b / 'data' / (name + '-audit.json') for b in [HERE, PREV, OLD]]
        candidates = [p for p in candidates if p.exists()]
        assert any(sha(p) == digest for p in candidates), (module, name)
    return dict(module=module, receipt=path.relative_to(ROOT).as_posix(),
                receipt_sha256=sha(path), theorem_audits=len(r['theorem_audits']),
                seconds=r['seconds'])


modules = [check_module(HERE, p) for p in sorted((HERE / 'data').glob('*-audit.json'))
           if 'module' in read(p)]
names = {r['module'] for r in modules}
assert {'WitnessLookup', 'WitnessTablesData', 'WitnessTablesChecks',
        'Class001WitnessData', 'Class001WitnessChecks', 'WitnessFactors'} <= names
audits = sum(r['theorem_audits'] for r in modules)
for name, script in [('witness-table-generation.json', 'build_witness_tables.py'),
                     ('class001-generation.json', 'build_class001.py'),
                     ('witness-batch-plan.json', 'plan_witness_batches.py'),
                     ('witness-factor-profile.json', 'profile_witness_factors.py')]:
    r = read(HERE / 'data' / name)
    assert sha(HERE / 'scripts' / script) == r['script_sha256']
    for path, digest in r['input_sha256'].items():
        assert sha(ROOT / path) == digest, path
    for name, digest in r.get('source_sha256', {}).items():
        assert sha(HERE / 'lean' / name) == digest
plan = read(HERE / 'data/witness-batch-plan.json')
profile = read(HERE / 'data/witness-factor-profile.json')
assert plan['status'] == 'PASS_DETERMINISTIC_WITNESS_JOB_PLAN'
assert len(plan['base_jobs']) == 507 and len(plan['history_jobs']) == 3
assert profile['status'] == 'PASS_PLANNED_WITNESS_FACTOR_PROFILE'
assert profile['summary']['planned_entries_compared'] == 357823

previous = PREV / 'data/checkpoint.json'
old = read(previous)
old_proofs = read(PREV / 'data/proof-summary.json')
prior_geometry_modules = {r['module'] for r in old_proofs['modules']}
geometry_modules, geometry_classes, geometry_files = [], [], []
# A receipt appears only after a successful object and complete log are saved.
for p in sorted((PREV / 'data').glob('*-audit.json')):
    if re.fullmatch(r'(?:Balanced\d{3}|Cover\d{3})(?:Data|Checks)-audit.json', p.name):
        r = check_module(PREV, p)
        geometry_modules.append(r)
        match = re.fullmatch(r'Balanced(\d{3})Checks', r['module'])
        if match:
            geometry_classes.append(int(match[1]))
        if r['module'] not in prior_geometry_modules:
            geometry_files += [p, PREV / 'logs' / (r['module'] + '.log'),
                               PREV / 'logs' / (r['module'] + '-record.json')]
geometry = dict(status='OBSERVED_SUCCESSFUL_GEOMETRY_MODULES',
                observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                classes=sorted(geometry_classes), modules=geometry_modules,
                new_theorem_audits=sum(r['theorem_audits'] for r in geometry_modules
                                      if r['module'] not in prior_geometry_modules),
                archive_paths=[p.relative_to(ROOT).as_posix() for p in geometry_files],
                scope='Successful immutable receipts at this observation. The active batch may complete more later.')
(HERE / 'data/geometry-observation.json').write_text(json.dumps(geometry, indent=2) + '\n')
run_observations = []
for p in [*sorted((PREV / 'logs').glob('balanced-cover-run-*.json')),
          PREV / 'logs/case7302-unique-resume-run.json']:
    raw, r = stable_read(p)
    target = HERE / 'data' / ('snapshot-' + p.name)
    target.write_bytes(raw)
    run_observations.append(dict(original=p.relative_to(ROOT).as_posix(), snapshot=target.name,
                                 sha256=sha(target), status=r['status'], active=r.get('active')))

case = ROOT / 'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case / 'data/proof-audit.json').exists(), 'Case completed: refresh final proof status'
raw, live = stable_read(case / 'logs/completion-record.json')
(HERE / 'data/case7302-completion-observation.json').write_bytes(raw)
successful = {r['module']: r for r in live['records'] if r['exit_code'] == 0}
prior = {r['module']: r for r in old['case7302_successful_rows']}
rows, new_rows = [], []
archive = HERE / 'data/case7302-successful-log-snapshot.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as out:
    for name, row in successful.items():
        log = case / 'logs' / (name.replace('/', '-') + '.log')
        raw = log.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        assert 'error:' not in raw.decode() and 'sorryAx' not in raw.decode()
        if name in prior:
            checked = prior[name]
            assert checked['source_sha256'] == row['source_sha256'] and checked['log_sha256'] == digest
            objhash = checked['object_sha256']
            origin = 'Inherited object hash from pinned milestone89 checkpoint; not rehashed in this delta'
        else:
            assert sha(case / 'lean' / (name + '.lean')) == row['source_sha256']
            objhash = sha(Path(live['build']) / (name + '.olean'))
            new_rows.append(name)
            origin = 'Source and object bytes hashed in milestone90'
        info = zipfile.ZipInfo(log.name, (1980, 1, 1, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        out.writestr(info, raw)
        rows.append(dict(module=name, source_sha256=row['source_sha256'], object_sha256=objhash,
                         object_hash_scope=origin, log_sha256=digest, log_archive_member=log.name))
assert set(prior) <= set(successful)
with zipfile.ZipFile(archive) as saved:
    for row in rows:
        assert hashlib.sha256(saved.read(row['log_archive_member'])).hexdigest() == row['log_sha256']
paper = ROOT / 'paper/snake9_research.tex'
editor = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper) == sha(editor) == old['paper_sha256']
summary = dict(status='PASS_WITNESS_PILOT_AND_GENERIC_FACTORIZATION', theorem_audits=audits,
               modules=modules, concrete_numeric_membership_directions=[1,3,307,308,310,312],
               concrete_class=1, witness_lists=2, boxes=640, concrete_validity_entries=3840,
               bounded_histories='All q < 75 under the original numericKeep predicate',
               total_contexts=791, base_validity_jobs=507, separate_history_heads=3,
               full_context_assignment_checked=False, full_witness_validity_checked=False,
               factor_profile_summary=profile['summary'], concrete_factor_assembly_checked=False,
               profile_sha256=sha(HERE / 'data/witness-factor-profile.json'),
               plan_sha256=sha(HERE / 'data/witness-batch-plan.json'),
               observed_geometry_classes=sorted(geometry_classes),
               newly_observed_geometry_audits=geometry['new_theorem_audits'],
               reference_premises=['AllRefuted6K235', 'AllRefuted236'],
               scope='Checked generic lookup/factor identities, exact lookup tables, and six-direction membership pilot. '
                     'The all-entry factor profile and job plan are computational. No new bound or full graph interpretation.')
(HERE / 'data/proof-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
command = "@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and ($_.CommandLine -like '*case7302*' -or $_.CommandLine -like '*89-shared-cover-certification*') } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
output = subprocess.check_output(['powershell', '-NoProfile', '-Command', command], text=True).strip()
processes = json.loads(output) if output else []
if isinstance(processes, dict):
    processes = [processes]
refs = {ref: subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'rev-parse', ref],
                                    cwd=ROOT, text=True).strip() for ref in ['HEAD', 'origin/main']}
checkpoint = dict(status=summary['status'], recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  theorem_audits=audits, proof_summary_sha256=sha(HERE / 'data/proof-summary.json'),
                  observed_geometry_classes=sorted(geometry_classes), run_observations=run_observations,
                  geometric_batch_tool_session=23168, replay_tool_session=14427,
                  authoritative_process_observations=processes,
                  case7302_complete=False, case7302_successful_rows=rows,
                  case7302_raw_successful_record_count=sum(r['exit_code'] == 0 for r in live['records']),
                  case7302_distinct_successful_modules=len(rows), case7302_new_successful_modules=new_rows,
                  case7302_failed_attempts=[r for r in live['records'] if r['exit_code'] != 0],
                  case7302_successful_logs_sha256=sha(archive),
                  case7302_prior_checkpoint=previous.relative_to(ROOT).as_posix(), case7302_prior_checkpoint_sha256=sha(previous),
                  unconditional_edge_interval=[191,235], conditional_target=234,
                  upper_bound_evidence='Inspected contributor theorem and saved audit; no full independent rebuild.',
                  pending_target_cases=[7301,7302,7303,7307,7308], paper_revision=86,
                  next_scheduled_paper_revision=96, paper_sha256=sha(paper), git_refs_before_commit=refs,
                  next_task='Benchmark normalized reference-shape reuse on the same class1 jobs before expanding '
                            'the 507-job witness batch. Continue both existing background runs. Then certify '
                            'context assignment, full-key membership and endpoints; keep remaining premises explicit.')
(HERE / 'data/checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
print(summary['status'], audits, 'audits;', len(geometry_classes), 'observed geometry classes;',
      len(rows), 'distinct replay modules')
