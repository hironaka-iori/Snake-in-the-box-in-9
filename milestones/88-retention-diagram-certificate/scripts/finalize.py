"""Verify owned proofs and data, then freeze a delta of the existing replay."""
from pathlib import Path
import datetime, gzip, hashlib, json, re, subprocess, time, zipfile

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
read = lambda p: json.loads(p.read_text())


def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


counts = dict(Boxes=2, DigitReconstruction=5, BoxWitness=8, CoverTree=4,
              CoverageAssembly=4, GraphData=0, Case000Data=0, Case000Checks=3)
receipts = []
for module, expected in counts.items():
    p = HERE / 'data' / (module + '-audit.json')
    r = read(p)
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    source = HERE / 'lean' / (module + '.lean')
    assert sha(source) == r['source_sha256']
    assert sha(HERE / 'build' / (module + '.olean')) == r['olean_sha256']
    assert sha(HERE / 'logs' / (module + '.log')) == r['log_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b', source.read_text())
    assert len(r['theorem_audits']) == expected
    assert all(set(x['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
               for x in r['theorem_audits'])
    for dependency, digest in r.get('dependencies', r.get('dependency_receipts', {})).items():
        assert sha(HERE / 'data' / (dependency + '-audit.json')) == digest
    receipts.append(dict(module=module, receipt=p.name, sha256=sha(p), audits=expected))

baseline = read(HERE / 'data/box-cover-baseline-source.json')
baseline_bytes = baseline['source'].replace('\n', '\r\n').encode()
assert baseline['line_endings'] == 'CRLF'
assert hashlib.sha256(baseline_bytes).hexdigest() == baseline['source_sha256']
for suffix in ['', '-max-gain']:
    r = read(HERE / 'data' / ('box-cover-audit' + suffix + '.json'))
    assert r['status'] == 'PASS_EXACT_REJECTION_BOX_COVER'
    payload = HERE / 'data' / ('box-cover-selected' + suffix + '.json.gz')
    assert sha(payload) == r['payload_sha256']
    assert hashlib.sha256(gzip.decompress(payload.read_bytes())).hexdigest() == r['payload_raw_sha256']
    assert r['all_complements_equal_saved_and_dag']
    assert r['all_selected_boxes_have_original_witness'] and r['all_selected_boxes_have_private_code']
    for rel, digest in r['input_sha256'].items():
        assert sha(ROOT / rel) == digest, rel
    expected = sha(HERE / 'scripts/build_boxes.py') if suffix else baseline['source_sha256']
    assert expected == r['script_sha256']
common = read(HERE / 'data/box-cover-audit-max-gain.json')
assert common['mask_classes'] == common['classes_with_full_common_geometry_cover'] == 127
assert common['class_missing_codes'] == 0 and common['class_selected_occurrences'] == 82659
pilot = read(HERE / 'data/pilot000-generation.json')
for name, digest in pilot['source_sha256'].items():
    assert sha(HERE / 'lean' / name) == digest
for name, digest in pilot['input_sha256'].items():
    path = ROOT / name if name.startswith('milestones') else HERE / 'data' / name
    assert sha(path) == digest
assert sha(HERE / 'data/pilot000-certificate.json.gz') == pilot['certificate_sha256']
assert sha(HERE / 'scripts/build_pilot.py') == pilot['script_sha256']
assert read(HERE / 'data/Case000Checks-audit.json')['status'] == 'PASS_PILOT_KERNEL_CERTIFICATE'

previous = ROOT / 'milestones/87-retained-array-membership/data/checkpoint.json'
old = read(previous)
paper = ROOT / 'paper/snake9_research.tex'
editor = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper) == sha(editor) == old['paper_sha256']
summary = dict(
    status='PASS_GENERIC_BOX_COVER_AND_ONE_KERNEL_PILOT', theorem_audits=sum(counts.values()),
    modules=receipts, paper_unchanged_sha256=sha(paper),
    pilot=dict(direction=0, history=0, boxes=375, accepted_codes=6123,
               unique_tree_nodes=723, expanded_node_visits=11869,
               receipt_sha256=sha(HERE / 'data/Case000Checks-audit.json'),
               status='PASS_PILOT_KERNEL_CERTIFICATE'),
    computational=dict(compatible_contexts=791, membership_classes=127,
                       shared_cover_box_occurrences=82659, context_witness_lists_materialized=False,
                       receipt_sha256=sha(HERE / 'data/box-cover-audit-max-gain.json')),
    reference_premises=['AllRefuted6K235', 'AllRefuted236'],
    remaining_structural_premises=[
        'Concrete witnesses and covers for all compatible contexts',
        'Diagram membership implies saved full-key row membership',
        'Concrete source-column and target-column identities'],
    scope='Generic rejection and coverage chain plus one concrete context checked in Lean. '
          'All-context box sharing is computational. No closed full finite coverage, '
          'weight interpretation, complete potential replay or new global bound. '
          'Inherited support objects reused without a full rebuild.')
(HERE / 'data/proof-summary.json').write_text(json.dumps(summary, indent=2) + '\n')

case = ROOT / 'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case / 'data/proof-audit.json').exists(), 'Case7302 completed: refresh pending claims'
for attempt in range(10):
    try:
        raw = (case / 'logs/completion-record.json').read_bytes()
        live = json.loads(raw)
        break
    except json.JSONDecodeError:
        if attempt == 9:
            raise
        time.sleep(.1)
(HERE / 'data/case7302-completion-observation.json').write_bytes(raw)
prior = {r['module']: r for r in old['case7302_successful_rows']}
rows, new_rows = [], []
archive = HERE / 'data/case7302-successful-log-snapshot.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as out:
    for row in live['records']:
        if row['exit_code'] != 0:
            continue
        name = row['module']
        log = case / 'logs' / (name.replace('/', '-') + '.log')
        data = log.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        assert 'error:' not in data.decode('utf-8') and 'sorryAx' not in data.decode('utf-8')
        if name in prior:
            checked = prior[name]
            assert checked['source_sha256'] == row['source_sha256'] and checked['log_sha256'] == digest
            objhash = checked['object_sha256']
            origin = 'Reused object hash from pinned milestone87; object bytes not rehashed in this delta snapshot'
        else:
            src = case / 'lean' / (name + '.lean')
            obj = Path(live['build']) / (name + '.olean')
            assert sha(src) == row['source_sha256']
            objhash = sha(obj)
            new_rows.append(name)
            origin = 'Source and object bytes hashed in milestone88'
        info = zipfile.ZipInfo(log.name, (1980, 1, 1, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        out.writestr(info, data)
        rows.append(dict(module=name, source_sha256=row['source_sha256'], object_sha256=objhash,
                         object_hash_scope=origin, log_sha256=digest, log_archive_member=log.name))
assert set(prior) <= {r['module'] for r in rows}
with zipfile.ZipFile(archive) as saved:
    for row in rows:
        assert hashlib.sha256(saved.read(row['log_archive_member'])).hexdigest() == row['log_sha256']
command = "@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7302*' } | Select-Object ProcessId,ParentProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
output = subprocess.check_output(['powershell', '-NoProfile', '-Command', command], text=True).strip()
processes = json.loads(output) if output else []
if isinstance(processes, dict):
    processes = [processes]
refs = {ref: subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'rev-parse', ref],
                                    cwd=ROOT, text=True).strip() for ref in ['HEAD', 'origin/main']}
checkpoint = dict(
    status=summary['status'], recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    proof_summary_sha256=sha(HERE / 'data/proof-summary.json'), theorem_audits=sum(counts.values()),
    unconditional_edge_interval=[191, 235], conditional_target=234,
    upper_bound_evidence='Inspected contributor theorem and saved audit; no fresh full independent rebuild.',
    paper_revision=86, next_scheduled_paper_revision=96, paper_sha256=sha(paper),
    git_refs_before_commit=refs, case7302_complete=False, case7302_successful_rows=rows,
    case7302_new_successful_modules=new_rows, case7302_prior_checkpoint=previous.relative_to(ROOT).as_posix(),
    case7302_prior_checkpoint_sha256=sha(previous), case7302_successful_logs_sha256=sha(archive),
    case7302_observed_processes=processes, proof_replay_tool_session=75639,
    pending_target_cases=[7301, 7302, 7303, 7307, 7308],
    next_task='Generate and certify the 127 shared covers and context-specific witnesses, '
              'then connect diagram membership to the full-key rows and endpoint columns. '
              'Reuse the checked generic chain and pilot. Preserve the existing case7302 replay.')
(HERE / 'data/checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
print(summary['status'], sum(counts.values()), 'audits;', len(rows), 'successful replay rows,',
      len(new_rows), 'new since87')
