"""Freeze completed proofs and authoritative observations of the two live jobs."""
from pathlib import Path
import datetime, gzip, hashlib, json, re, subprocess, time, zipfile

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
OLD = ROOT / 'milestones/88-retention-diagram-certificate'
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))


def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for part in iter(lambda: f.read(1024 * 1024), b''):
            h.update(part)
    return h.hexdigest()


def stable_read(p):
    for attempt in range(10):
        try:
            raw = p.read_bytes()
            return raw, json.loads(raw)
        except json.JSONDecodeError:
            if attempt == 9:
                raise
            time.sleep(.1)


modules, audits, classes = [], 0, []
for path in sorted((HERE / 'data').glob('*-audit.json')):
    _, r = stable_read(path)
    if 'module' not in r:
        continue
    module = r['module']
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    src = HERE / 'lean' / (module + '.lean')
    assert sha(src) == r['source_sha256']
    assert sha(HERE / 'build' / (module + '.olean')) == r['olean_sha256']
    assert sha(HERE / 'logs' / (module + '.log')) == r['log_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b', src.read_text())
    assert len(r['theorem_audits']) == src.read_text().count('#print axioms')
    for row in r['theorem_audits']:
        assert set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    for dep, digest in r.get('dependencies', r.get('dependency_receipts', {})).items():
        if dep.startswith('milestones'):
            dp = ROOT / dep
        else:
            dp = HERE / 'data' / (dep + '-audit.json')
            if not dp.exists():
                dp = OLD / 'data' / (dep + '-audit.json')
        assert sha(dp) == digest, (module, dep)
    n = len(r['theorem_audits'])
    audits += n
    modules.append(dict(module=module, receipt=path.name, sha256=sha(path), audits=n))
    match = re.fullmatch(r'Balanced(\d{3})Checks', module)
    if match:
        classes.append(int(match[1]))
assert 1 in classes
for name, script in [('context-witnesses-audit.json', 'materialize_witnesses.py'),
                     ('shared-cover-generation.json', 'build_shared_covers.py'),
                     ('balanced-cover-generation.json', 'build_balanced_covers.py')]:
    r = read(HERE / 'data' / name)
    assert sha(HERE / 'scripts' / script) == r['script_sha256']
    for rel, digest in r['input_sha256'].items():
        assert sha(ROOT / rel) == digest, rel
wr = read(HERE / 'data/context-witnesses-audit.json')
assert wr['status'] == 'PASS_ALL_CONTEXT_WITNESSES' and wr['independent_validations'] == 543827
assert sha(HERE / 'data/context-witnesses.json.gz') == wr['payload_sha256']
assert hashlib.sha256(gzip.decompress((HERE / 'data/context-witnesses.json.gz').read_bytes())).hexdigest() == wr['payload_raw_sha256']
for r in read(HERE / 'data/shared-cover-generation.json')['classes']:
    label = f"{r['dag_set']:03d}"
    assert sha(HERE / 'data' / f'cover{label}-certificate.json.gz') == r['certificate_sha256']
    for name, digest in r['source_sha256'].items():
        assert sha(HERE / 'lean' / name) == digest
for name, digest in read(HERE / 'data/balanced-cover-generation.json')['source_sha256'].items():
    assert sha(HERE / 'lean' / name) == digest

previous = OLD / 'data/checkpoint.json'
old = read(previous)
paper = ROOT / 'paper/snake9_research.tex'
editor = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper) == sha(editor) == old['paper_sha256']
run_observations = []
for p in sorted((HERE / 'logs').glob('balanced-cover-run-*.json')):
    raw, r = stable_read(p)
    target = HERE / 'data' / ('snapshot-' + p.name)
    target.write_bytes(raw)
    run_observations.append(dict(original=p.relative_to(HERE).as_posix(), snapshot=target.name,
                                 sha256=sha(target), status=r['status'], active=r.get('active')))
rp = HERE / 'logs/case7302-unique-resume-run.json'
raw, resumed = stable_read(rp)
(HERE / 'data/case7302-resume-observation.json').write_bytes(raw)

summary = dict(status='PASS_SHARED_COVER_INFRASTRUCTURE_PARTIAL_FINITE_BATCH',
               theorem_audits=audits, modules=modules, checked_geometric_classes=sorted(classes),
               total_geometric_classes=127, all_context_witness_equations_checked=False,
               materialized_contexts=791, materialized_witness_occurrences=543827,
               unique_aligned_witness_lists=211, computed_shared_box_occurrences=82659,
               finite_pointwise_checks=5925312, reference_premises=['AllRefuted6K235', 'AllRefuted236'],
               paper_unchanged_sha256=sha(paper),
               remaining=['Remaining geometric class equations', 'Concrete witness equations and context assignment',
                          'Diagram-to-full-key-row membership and endpoint identities',
                          'Closed reference catalogue premises', 'Credit interpretation, pending shares and full potential'],
               scope='Generic history transport, separated witness assembly, lookup equivalences and the listed '
                     'concrete geometric classes checked in Lean. All-context witness data is computational. '
                     'No new global bound or complete graph interpretation.')
(HERE / 'data/proof-summary.json').write_text(json.dumps(summary, indent=2) + '\n')

case = ROOT / 'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case / 'data/proof-audit.json').exists(), 'Replay completed: refresh final theorem status'
raw, live = stable_read(case / 'logs/completion-record.json')
(HERE / 'data/case7302-completion-observation.json').write_bytes(raw)
# The inherited driver appends composition rows on each resume. Count modules once.
successful = {r['module']: r for r in live['records'] if r['exit_code'] == 0}
prior = {r['module']: r for r in old['case7302_successful_rows']}
rows, new_rows = [], []
archive = HERE / 'data/case7302-successful-log-snapshot.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as out:
    for name, row in successful.items():
        log = case / 'logs' / (name.replace('/', '-') + '.log')
        data = log.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        assert 'error:' not in data.decode() and 'sorryAx' not in data.decode()
        if name in prior:
            checked = prior[name]
            assert checked['source_sha256'] == row['source_sha256'] and checked['log_sha256'] == digest
            objhash = checked['object_sha256']
            origin = 'Reused object hash from pinned milestone88; object bytes not rehashed in this delta snapshot'
        else:
            assert sha(case / 'lean' / (name + '.lean')) == row['source_sha256']
            objhash = sha(Path(live['build']) / (name + '.olean'))
            new_rows.append(name)
            origin = 'Source and object bytes hashed in milestone89'
        info = zipfile.ZipInfo(log.name, (1980, 1, 1, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        out.writestr(info, data)
        rows.append(dict(module=name, source_sha256=row['source_sha256'], object_sha256=objhash,
                         object_hash_scope=origin, log_sha256=digest, log_archive_member=log.name))
assert set(prior) <= set(successful)
with zipfile.ZipFile(archive) as saved:
    for row in rows:
        assert hashlib.sha256(saved.read(row['log_archive_member'])).hexdigest() == row['log_sha256']
command = "@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and ($_.CommandLine -like '*case7302*' -or $_.CommandLine -like '*89-shared-cover-certification*') } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
output = subprocess.check_output(['powershell', '-NoProfile', '-Command', command], text=True).strip()
processes = json.loads(output) if output else []
if isinstance(processes, dict):
    processes = [processes]
refs = {ref: subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'rev-parse', ref],
                                    cwd=ROOT, text=True).strip() for ref in ['HEAD', 'origin/main']}
checkpoint = dict(status=summary['status'], recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  theorem_audits=audits, proof_summary_sha256=sha(HERE / 'data/proof-summary.json'),
                  checked_geometric_classes=sorted(classes), shared_cover_run_observations=run_observations,
                  geometric_batch_tool_session=23168, replay_tool_session=14427,
                  authoritative_process_observations=processes,
                  case7302_complete=False, case7302_successful_rows=rows,
                  case7302_raw_successful_record_count=sum(r['exit_code'] == 0 for r in live['records']),
                  case7302_distinct_successful_modules=len(rows), case7302_new_successful_modules=new_rows,
                  case7302_failed_attempts=[r for r in live['records'] if r['exit_code'] != 0],
                  case7302_successful_logs_sha256=sha(archive),
                  case7302_prior_checkpoint=previous.relative_to(ROOT).as_posix(), case7302_prior_checkpoint_sha256=sha(previous),
                  case7302_resume_status=resumed['status'],
                  unconditional_edge_interval=[191,235], conditional_target=234,
                  upper_bound_evidence='Inspected contributor theorem and saved audit; no full independent rebuild.',
                  pending_target_cases=[7301,7302,7303,7307,7308], paper_revision=86,
                  next_scheduled_paper_revision=96, paper_sha256=sha(paper), git_refs_before_commit=refs,
                  next_task='Continue the existing sequential balanced-cover batch. Verify concrete context witnesses '
                            'using shared geometry and history transport, then close context assignment and full-key indexing. '
                            'Inspect the resumed case7302 driver before any restart.')
(HERE / 'data/checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
print(summary['status'], audits, 'audits;', len(classes), 'geometric classes;', len(rows), 'distinct replay modules')
