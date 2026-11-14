"""Read-only saved-record audit. Execute only after the parent confirms the native batch is terminal.
A FOUND witness deliberately requires separate assignment and geometry review.
"""
from pathlib import Path
from collections import Counter
import hashlib, json

H = Path(__file__).resolve().parents[1]
P = H.parent / '214-parity-partner-capacity'
F, OLD = H / 'data/case-22', P / 'data/case-22'

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def sha(path):
    return digest(path.read_bytes())

def read(path):
    return json.loads(path.read_bytes())

def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode('utf-8')

def pins(root, mapping):
    for name, expected in mapping.items():
        assert sha(root / name) == expected, str(root / name)

def disjoint(regions):
    comparisons = 0
    for i, a in enumerate(regions):
        for b in regions[i + 1:]:
            assert any(not (x & y) for x, y in zip(a, b))
            comparisons += 1
    return comparisons

transfer = read(H / 'data/frontier-transfer.json')
source = read(OLD / 'state.json')
initial_raw = (F / 'initial-state.json').read_bytes()
initial = json.loads(initial_raw)
assert not (H / 'data/history-search.lock').exists(), 'Only audit after the parent terminal notice'
final_raw = (F / 'state.json').read_bytes()
final = json.loads(final_raw)
summary = read(H / 'data/search-summary.json')
assert Path(transfer['source_milestone']) == P
assert sha(OLD / 'state.json') == transfer['source_state_sha256']
assert (F / 'transfer214-state.json').read_bytes() == (OLD / 'state.json').read_bytes()
assert (F / 'transfer214-initial-state.json').read_bytes() == (OLD / 'initial-state.json').read_bytes()
assert {str(p.relative_to(OLD)) for p in OLD.rglob('*') if p.is_file()} == set(transfer['source_files_sha256'])
for name, expected in transfer['source_files_sha256'].items():
    target = transfer['source_file_aliases'].get(name, name)
    assert sha(OLD / name) == expected == sha(F / target), name
assert source['committed_jobs'] == transfer['source_jobs'] == 240
assert source['nodes'] == transfer['source_nodes']
assert source['seconds'] == transfer['source_seconds']
assert len(source['frontier']) == transfer['frontier_regions'] == 13
assert source['status'] == 'OPEN'
expected_initial = json.loads((OLD / 'state.json').read_bytes())
expected_initial['engine_pins'] = transfer['new_engine_pins']
expected_initial['transfer_record'] = 'data/frontier-transfer.json'
assert encoded(expected_initial) == initial_raw
assert digest(initial_raw) == transfer['transferred_state_sha256']
assert all(initial[k] == source[k] for k in transfer['unchanged_fields'])
assert source['engine_pins'] == transfer['old_engine_pins']
pins(P, source['engine_pins']); pins(OLD, source['model_pins'])
pins(H, initial['engine_pins']); pins(F, initial['model_pins'])
assert sha(H / 'data/PathWordCapacity215-audit.json') == transfer['proof_receipt_sha256']
assert sha(H / 'logs/word-engine-review.md') == transfer['source_review_sha256']
proof = read(H / 'data/PathWordCapacity215-audit.json')
assert proof['status'] == 'PASS' and proof['exit_code'] == 0 and proof['stop_reason'] is None
for filekey, hashkey in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
    assert sha(Path(proof[filekey])) == proof[hashkey]
for path, expected in proof['dependencies'].items():
    assert sha(Path(path)) == expected

source_jobs = transfer['source_jobs']
assert len(transfer['source_files_sha256']) == 1448
assert transfer['source_file_aliases'] == {'state.json':'transfer214-state.json', 'initial-state.json':'transfer214-initial-state.json'}
assert final['receipts'][:source_jobs] == initial['receipts'] == source['receipts']
new_receipts = final['receipts'][source_jobs:]
new_count = len(new_receipts)
assert 0 <= new_count <= 500 and len(set(final['receipts'])) == source_jobs + new_count
extra_receipts = {str(p.relative_to(H)) for p in F.glob('run-*/receipt.json')} - set(final['receipts'])
for name in extra_receipts:
    extra = read(H / name)
    assert extra['status'] == 'NOT_COMMITTED', name
    assert extra['state_before_sha256'] == digest(final_raw), name
    assert (H / name).with_name('state-before.json').read_bytes() == final_raw
    assert not (H / name).with_name('state-after.json').exists()
model = read(F / 'model.json'); permutations = read(F / 'permutations.json')
tail = (F / 'input-tail.txt').read_bytes()
current_raw, current = initial_raw, initial
statuses, totals, budgets = Counter(), Counter(), Counter()
pending_returned = 0
local_disjoint = 0
frontier_disjoint = disjoint([x['domains'] for x in initial['frontier']])
gate_free, sample_free, private = [], [], []
transition_rows = []
for offset, name in enumerate(new_receipts):
    path = H / name; run = path.parent
    receipt, result = read(path), read(run / 'stdout.json')
    assert run.name.split('-')[1] == str(source_jobs + offset)
    assert (run / 'state-before.json').read_bytes() == current_raw
    assert receipt['state_before_sha256'] == digest(current_raw)
    assert current['status'] == 'OPEN' and current['frontier']
    job = current['frontier'][-1]; domains = job['domains']
    assert receipt['job_id'] == job['id']
    assert len(domains) == model['variables']
    assert all(x and x & root == x for x, root in zip(domains, model['domains']))
    head = (run / 'input-head.txt').read_bytes(); lines = head.decode('ascii').splitlines()
    seconds, nodes = lines[1].split(); seconds, nodes = float(seconds), int(nodes)
    assert seconds > 0 and nodes > 0
    expected_head = (f'{model["variables"]} 64 {len(model["constraints"])} {len(model["nogoods"])} {len(permutations)}\n'
                     f'{seconds} {nodes}\n' + ' '.join(map(str, domains)) + '\n').encode('ascii')
    assert head == expected_head and receipt['input_sha256'] == digest(head + tail)
    budgets[f'{seconds} seconds / {nodes} nodes'] += 1
    assert receipt['engine_pins'] == current['engine_pins'] == initial['engine_pins']
    assert receipt['model_pins'] == current['model_pins'] == initial['model_pins']
    assert receipt['status'] == 'ACCEPTED_TRANSITION' and receipt['exit_code'] == 0
    assert receipt['hard_stop'] is False
    if receipt['stop_reason'] is not None:
        assert offset == new_count - 1, 'Only the final committed job may carry a resource stop'
    assert (run / 'stderr.txt').read_bytes() == b''
    assert receipt['stdout_sha256'] == sha(run / 'stdout.json')
    gate = receipt['resource_gate']
    assert not gate['errors'] and not gate['processes'] and gate['free_bytes'] >= 1024**3
    gate_free.append(gate['free_bytes'])
    for sample in receipt['resource_samples']:
        sample_free.append(sample['free_bytes'])
        if sample['private_bytes'] is not None:
            private.append(sample['private_bytes'])
    status, pending = result['status'], result['pending']
    assert status in ['EXHAUSTED', 'LIMIT'], 'A FOUND witness needs a separate assignment and geometry review before acceptance here'
    assert result['solution'] is None
    assert bool(pending) == (status == 'LIMIT')
    assert receipt['solver_status'] == status and receipt['returned_frontier'] == len(pending)
    assert receipt['nodes'] == result['nodes'] and receipt['solver_seconds'] == result['seconds']
    assert isinstance(result['nodes'], int) and result['nodes'] > 0 and result['seconds'] >= 0
    for part in pending:
        assert len(part) == model['variables']
        assert all(x and x & old == x for x, old in zip(part, domains))
    local_disjoint += disjoint(pending)
    after = json.loads(current_raw)
    after['committed_jobs'] += 1; after['nodes'] += result['nodes']; after['seconds'] += result['seconds']
    rest, children = after['frontier'][:-1], []
    for part in pending:
        children.append({'id': after['next_id'], 'domains': part}); after['next_id'] += 1
    after['frontier'] = rest + list(reversed(children))
    after['status'] = 'OPEN' if after['frontier'] else 'EXHAUSTED'
    after['receipts'].append(name)
    assert len({x['id'] for x in after['frontier']}) == len(after['frontier'])
    assert all(x['id'] < after['next_id'] for x in after['frontier'])
    frontier_disjoint += disjoint([x['domains'] for x in after['frontier']])
    raw = encoded(after)
    assert raw == (run / 'state-after.json').read_bytes()
    assert receipt['state_after_sha256'] == digest(raw)
    statuses[status] += 1; pending_returned += len(pending)
    for key, value in result.items():
        if isinstance(value, (int, float)):
            totals[key] += value
    entry = summary['new_receipts'][offset]
    assert entry == {'receipt': name, 'sha256': sha(path), 'stop_reason': receipt['stop_reason']}
    transition_rows.append({'receipt': name, 'sha256': sha(path), 'before': digest(current_raw), 'after': digest(raw),
                            'stdout': sha(run / 'stdout.json'), 'input': digest(head + tail), 'status': status,
                            'job_id': job['id'], 'returned': len(pending), 'stop_reason': receipt['stop_reason']})
    current_raw, current = raw, after

assert current_raw == final_raw and current == final
assert final['status'] == summary['status'] and final['status'] in ['OPEN','EXHAUSTED']
assert final['committed_jobs'] == summary['jobs'] == source_jobs + new_count
assert summary['new_jobs'] == new_count and len(final['frontier']) == summary['pending']
assert final['nodes'] == summary['nodes'] and final['seconds'] == summary['seconds']
assert dict(statuses) == summary['new_statuses']
assert all(totals[key] == value for key, value in summary['new_operation_totals'].items())
assert len(summary['new_receipts']) == new_count and summary['state_sha256'] == digest(final_raw)
progress = read(H / 'data/word-search-progress.json')
assert progress['status'] in ['BUDGET','COMPLETE','RESOURCE_STOP','STARTUP_WAIT','INTERRUPTED']
stop_jobs = sum(x['stop_reason'] is not None for x in transition_rows)
assert progress['new_committed_jobs_without_resource_stop'] == new_count - stop_jobs
assert bool(stop_jobs) == (progress['status'] == 'RESOURCE_STOP')
assert bool(extra_receipts) == (progress['status'] == 'INTERRUPTED')
if progress['status'] == 'COMPLETE':
    assert final['status'] == 'EXHAUSTED' and not final['frontier']
assert progress['case_states']['22'] == {'status': final['status'], 'committed_jobs': final['committed_jobs'],
                                      'pending': len(final['frontier']), 'nodes': final['nodes'],
                                      'seconds': final['seconds'], 'state_sha256': digest(final_raw)}
assert progress['engine_pins'] == final['engine_pins']
assert len(initial['frontier']) - new_count + pending_returned == len(final['frontier'])
assert not (H / 'data/history-search.lock').exists(), 'Only audit after the terminal notice'
assert (F / 'state.json').read_bytes() == final_raw, 'Final state changed during the audit'
report = {'status': 'PASS_SAVED_TRANSFER_AND_NEW_TRANSITIONS', 'source_files': len(transfer['source_files_sha256']),
          'inherited_jobs': source_jobs, 'transferred_regions': len(initial['frontier']), 'new_jobs': new_count,
          'extra_uncommitted_receipts': sorted(extra_receipts), 'batch_stop': progress['status'], 'new_statuses': dict(statuses),
          'new_operation_totals': dict(totals), 'returned_regions': pending_returned,
          'pending_pair_comparisons': local_disjoint, 'all_frontier_pair_comparisons': frontier_disjoint,
          'budgets': dict(budgets), 'minimum_gate_free_bytes': min(gate_free, default=None),
          'minimum_sample_free_bytes': min(sample_free, default=None), 'maximum_private_bytes': max(private, default=None),
          'final': {'status': final['status'], 'jobs': final['committed_jobs'], 'pending': len(final['frontier']),
                    'ids': [x['id'] for x in final['frontier']], 'next_id': final['next_id'],
                    'nodes': final['nodes'], 'seconds': final['seconds'], 'sha256': digest(final_raw)},
          'source_state_sha256': sha(OLD / 'state.json'), 'transferred_state_sha256': digest(initial_raw),
          'source_pins': {name: sha(H / name) for name in ['scripts/audit_saved_chain.py','scripts/word_continue.py',
                         'scripts/transfer_frontier.py','scripts/word_solver.c','data/frontier-transfer.json',
                         'data/search-summary.json','data/word-search-progress.json','data/PathWordCapacity215-audit.json',
                         'logs/word-engine-review.md']},
          'engine_pins': final['engine_pins'], 'model_pins': final['model_pins'], 'transitions': transition_rows,
          'scope': 'Saved-record reconstruction and native source premises; no solver rerun, compiler, software tests, or Lean traversal certificate. Pending containment/disjointness does not independently prove that native propagation and search omitted no satisfying assignment.'}
(H / 'data/chain-audit.json').write_bytes(encoded(report))
print(json.dumps({k:v for k,v in report.items() if k not in ['transitions','source_pins','engine_pins','model_pins']}, indent=2))
