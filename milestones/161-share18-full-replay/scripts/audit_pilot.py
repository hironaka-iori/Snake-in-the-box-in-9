"""Audit the first32 continuation segments; never assert full contradiction."""
from pathlib import Path
import hashlib
import json
import re

H = Path(__file__).resolve().parents[1]

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def read(p):
    return json.loads(Path(p).read_text(encoding='utf-8-sig'))

def main():
    ep = H / 'data/kernel-execution.json'
    plan = read(ep)
    source = read(H / 'data/full-source-plan.json')
    native_path = Path(source['transport_receipt'])
    if not native_path.is_absolute():
        native_path = H / native_path
    assert sha(native_path) == source['transport_receipt_sha256']
    native = read(native_path)
    assert native['status'] == 'PASS_COMPLETE_REMAINING_TRANSPORT_ONLY'
    assert not (H / 'data/replay-batch.lock').exists()
    progress = read(H / 'data/replay-progress.json')
    assert progress['status'] == 'PASS_PILOT_MODULES' and progress['pilot']
    assert progress['checked'] == plan['pilot_module_order']
    for p, d in plan['input_pins'].items():
        assert sha(p) == d, p
    receipts = {}
    reports = []
    checks = []
    peak = 0
    for module in plan['pilot_module_order']:
        rp = H / 'data' / (module + '-audit.json')
        row = read(rp)
        assert row['status'] == 'PASS' and row['exit_code'] == 0 and row['stop_reason'] is None
        for field, digest in [('source', 'source_sha256'), ('object', 'olean_sha256'), ('log', 'log_sha256')]:
            assert sha(row[field]) == row[digest], row[field]
        assert row['source_sha256'] == plan['source_sha256'][module]
        for p, d in row['dependencies'].items():
            assert sha(p) == d, p
        text = Path(row['source']).read_text(encoding='utf-8')
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', text)
        assert len(row['axioms']) == text.count('#print axioms')
        for report in row['axioms']:
            assert set(report['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
            reports.append(report)
        checks.extend(int(i) for i in re.findall(r'theorem ok(\d+)\s*:', text))
        for sample in row['resource_samples']:
            assert not sample['errors']
            for process in sample['processes']:
                if process['ProcessId'] == row['compiler_pid']:
                    peak = max(peak, process['PrivatePageCount'])
        receipts[str(rp.relative_to(H)).replace('\\', '/')] = sha(rp)
    assert sorted(checks) == list(range(32))
    assert any('pilot' in q['theorem'].lower() for q in reports)
    segments = native['segments'][:32]
    rows = segments[-1]['after_step']
    refs = sum(x['references'] for x in segments)
    result = dict(status='PASS_FIRST32_REMAINING_SEGMENTS',
                  execution_plan_sha256=sha(ep), source_plan_sha256=sha(H / 'data/full-source-plan.json'),
                  transport_receipt_sha256=sha(native_path), receipts=receipts,
                  module_count=len(receipts), axiom_reports=len(reports),
                  newly_checked_segments=32, newly_checked_deductions=rows,
                  newly_checked_references=refs, total_checked_deductions=1055 + rows,
                  total_checked_references=6006 + refs,
                  remaining_deductions=144160 - rows, remaining_references=14704875 - refs,
                  maximum_sampled_private_bytes=peak, full_share18_replay_complete=False,
                  actual_share18_theorem_complete=False, new_global_bound=False,
                  scope='Original CNF truth implies the checked checkpoint after the first32 continuation segments.',
                  auditor_sha256=sha(Path(__file__)))
    p = H / 'data/pilot-completion.json'
    b = (json.dumps(result, indent=2) + '\n').encode()
    if p.exists():
        assert p.read_bytes() == b
    else:
        p.write_bytes(b)
    print(json.dumps({k: v for k, v in result.items() if k != 'receipts'}, indent=2))

if __name__ == '__main__':
    main()
