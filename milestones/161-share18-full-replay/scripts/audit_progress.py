"""Audit accepted replay modules and the consecutive completed group prefix."""
from pathlib import Path
import argparse
import hashlib
import json
import re

H = Path(__file__).resolve().parents[1]

def read(p):
    return json.loads(Path(p).read_text(encoding='utf-8-sig'))

def digest(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--label', required=True)
    args = ap.parse_args()
    assert re.fullmatch(r'[a-zA-Z0-9_-]+', args.label)
    assert not (H / 'data/replay-batch.lock').exists()
    progress_path = H / 'data/replay-progress.json'
    progress = read(progress_path)
    progress_hash = digest(progress_path)
    assert progress['active'] is None
    assert progress['status'] in ['PASS_BOUNDED_REPLAY_PREFIX', 'PASS_COMPLETE_REPLAY_MODULES',
                                  'STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE']
    plan_path = H / 'data/kernel-execution.json'
    plan = read(plan_path)
    source = read(H / 'data/full-source-plan.json')
    expected = {}

    def expect(path, value):
        name = str(Path(path).resolve())
        assert name not in expected or expected[name] == value, name
        expected[name] = value

    for path, value in plan['input_pins'].items():
        expect(path, value)
    receipts = {}
    reports = []
    checked_segments = []
    peak = 0
    for module in plan['new_module_order']:
        rp = H / 'data' / (module + '-audit.json')
        if not rp.exists():
            continue
        row = read(rp)
        assert row['status'] == 'PASS' and row['exit_code'] == 0 and row['stop_reason'] is None
        assert row['source_sha256'] == plan['source_sha256'][module]
        for field, key in [('source', 'source_sha256'), ('object', 'olean_sha256'), ('log', 'log_sha256')]:
            expect(row[field], row[key])
        for path, value in row['dependencies'].items():
            expect(path, value)
        text = Path(row['source']).read_text(encoding='utf-8')
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', text)
        assert len(row['axioms']) == text.count('#print axioms')
        for report in row['axioms']:
            assert set(report['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
            reports.append(report)
        checked_segments.extend(int(i) for i in re.findall(r'theorem ok(\d+)\s*:', text))
        for sample in row['resource_samples']:
            assert not sample['errors']
            for p in sample['processes']:
                if p['ProcessId'] == row['compiler_pid']:
                    peak = max(peak, p['PrivatePageCount'])
        receipts[module] = dict(path=rp.relative_to(H).as_posix(), sha256=digest(rp))
    assert set(progress['checked']) <= set(receipts)
    assert len(checked_segments) == len(set(checked_segments))
    groups = []
    for group in source['groups']:
        g = group['group']
        if f'ReplaySteps161_{g:04d}' not in receipts:
            break
        assert set(range(group['first_segment'], group['after_segment'])) <= set(checked_segments)
        assert any(q['theorem'] == f'Snake9.ReplayFull161.steps{g}' for q in reports)
        groups.append(group)
    assert groups and 'ReplayPilot161' in receipts
    for path, value in expected.items():
        assert digest(path) == value, path
    assert digest(progress_path) == progress_hash
    assert not (H / 'data/replay-batch.lock').exists()
    assert len(groups) < len(source['groups']), 'Use a complete-contradiction audit for the final group.'
    records = [p for p in (H / 'logs').glob('replay-batch-*.json') if digest(p) == progress_hash]
    assert len(records) == 1, 'Require the unique preserved terminal batch record.'
    deductions = groups[-1]['after_step']
    references = sum(g['references'] for g in groups)
    result = dict(status='PASS_BOUNDED_REPLAY_GROUPS',
                  execution_plan_sha256=digest(plan_path),
                  source_plan_sha256=digest(H / 'data/full-source-plan.json'),
                  progress_sha256=digest(progress_path), receipts=receipts,
                  progress_record=records[0].relative_to(H).as_posix(),
                  accepted_modules=len(receipts), axiom_reports=len(reports),
                  completed_groups=len(groups), completed_group_segments=groups[-1]['after_segment'],
                  all_checked_segments=sorted(checked_segments),
                  continuation_deductions_in_completed_groups=deductions,
                  continuation_references_in_completed_groups=references,
                  total_deductions_in_completed_groups=1055 + deductions,
                  total_references_in_completed_groups=6006 + references,
                  remaining_deductions=144160 - deductions,
                  remaining_references=14704875 - references,
                  maximum_sampled_private_bytes=peak,
                  full_share18_replay_complete=False, actual_share18_theorem_complete=False,
                  new_global_bound=False,
                  scope='Consecutive group implications and their segment checks are accepted. The pilot supplies the first group from the original clauses. Full contradiction assembly remains pending.',
                  auditor_sha256=digest(Path(__file__)))
    path = H / 'data' / ('progress-completion-' + args.label + '.json')
    payload = (json.dumps(result, indent=2) + '\n').encode()
    assert not path.exists()
    path.write_bytes(payload)
    print(json.dumps({k:v for k,v in result.items() if k not in ['receipts','all_checked_segments']}, indent=2))

if __name__ == '__main__':
    main()
