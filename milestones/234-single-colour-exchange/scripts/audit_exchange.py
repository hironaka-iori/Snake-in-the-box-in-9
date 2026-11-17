"""Independently reconstruct saved static decisions. No solver or compiler.

Run only after the parent authorizes the full audit and the native worker ends.
The producer mutates a 95-core graph; this audit instead counts exact label
neighbours in each resulting 96-set and forms its simple adjacency directly.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
CODES = ['CANDIDATE', 'ISOLATED', 'FEWER_THAN_TWO_PORTS',
         'TOO_MANY_LEAVES', 'UNSUPPORTED_LEAF', 'DISCONNECTED']


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def classify(selected_mask, vertex_order, neighbours, masks):
    """Exact classification of one full selected set, with early isolation exit.

    Every label of positive selected degree touches a selected vertex. Visiting
    the nine labels incident to each selected vertex therefore suffices. The
    cache is local to this one set and contains no producer graph state.
    """
    label_cache = {}
    adjacency = {}
    ports = set()
    leaves = []
    for v in vertex_order:
        vbit = 1 << v
        adjacent = 0
        endpoint_supported = False
        for z in neighbours[v]:
            entry = label_cache.get(z)
            if entry is None:
                selected = masks[z] & selected_mask
                entry = (selected, selected.bit_count())
                label_cache[z] = entry
            selected, degree = entry
            if degree == 1:
                # z touches v, which is selected, so v is its unique neighbour.
                endpoint_supported = True
            elif degree == 2:
                adjacent |= selected ^ vbit
        if adjacent == 0:
            return 1
        adjacency[v] = adjacent
        if endpoint_supported:
            ports.add(v)
        if adjacent.bit_count() == 1:
            leaves.append(v)
    if len(ports) < 2:
        return 2
    if len(leaves) > 2:
        return 3
    if any(v not in ports for v in leaves):
        return 4
    reached = 0
    pending = 1 << vertex_order[0]
    while pending:
        first = pending & -pending
        pending ^= first
        if reached & first:
            continue
        reached |= first
        pending |= adjacency[first.bit_length()-1] & ~reached
    return 0 if reached == selected_mask else 5


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--execute', action='store_true', required=True,
                        help='Explicitly start the full authorized reconstruction.')
    parser.add_argument('--tag', default='exchange')
    parser.add_argument('--seconds', type=float, default=1200)
    args = parser.parse_args()
    assert args.seconds > 0
    assert not (H/'data/forest-search.lock').exists(), 'Native worker still owns the slot'
    assert not (R/'work/fullgraph-active.lock').exists(), 'Full graph worker is active'
    destination = H/'data/exchange-audit.json'
    assert not destination.exists(), 'Preserve the existing audit receipt'
    source = H/'data/bases.json'
    saved = H/'data'/(args.tag+'.json')
    binary = H/'data'/(args.tag+'-decisions.bin')
    receipt_path = H/'data'/(args.tag+'-execution.json')
    pin_paths = [source, saved, binary, receipt_path, H/'scripts/exchange.py',
                 H/'scripts/run_exchange.py', H/'scripts/native_resources.py', Path(__file__)]
    pins = {str(p): sha(p) for p in pin_paths}
    raw = json.loads(source.read_bytes())
    data = json.loads(saved.read_bytes())
    execution = json.loads(receipt_path.read_bytes())
    assert raw == json.loads((R/'milestones/232-minority-contraction/data/bases.json').read_bytes())
    for path, digest in raw['pins'].items():
        assert sha(path) == digest
    bases = raw['bases']
    assert len(bases) == 145 and [b['id'] for b in bases] == list(range(145))
    assert data['status'] == 'COMPLETE_STATIC_COVER'
    assert data['arguments']['start_core'] == 0, 'A suffix is not a standalone full cover'
    assert data['arguments']['tag'] == args.tag
    assert data['source_sha256'] == sha(source)
    assert data['script_sha256'] == sha(H/'scripts/exchange.py')
    assert data['code_names'] == CODES
    assert data['next_core'] == 13920 and len(data['cores']) == 13920
    assert data['descriptions'] == 2227200 and data['decision_bytes'] == 2227200
    assert data['decisions_sha256'] == sha(binary)
    decisions = binary.read_bytes()
    assert len(decisions) == 2227200 and all(code < len(CODES) for code in decisions)
    assert {CODES[k]: v for k, v in collections.Counter(decisions).items()} == data['statuses']
    assert execution['status'] == 'ACCEPTED_NATIVE_RESULT'
    assert execution['exit_code'] == 0 and execution['stop_reason'] is None
    for path, digest in execution['pins'].items():
        assert sha(path) == digest
    assert execution['result_sha256'] == sha(saved)
    for suffix in ['stdout', 'stderr']:
        assert execution[suffix+'_sha256'] == sha(H/'logs'/(args.tag+'-'+suffix+'.log'))
    assert not (H/'logs'/(args.tag+'-stderr.log')).read_bytes()
    stdout = [json.loads(line) for line in (H/'logs'/(args.tag+'-stdout.log')).read_text().splitlines() if line]
    assert len(stdout) == 146
    final_stdout = stdout[-1]
    for key in ['status', 'next_core', 'descriptions', 'statuses', 'seconds']:
        assert final_stdout[key] == data[key]
    assert all(not s['errors'] and not s['lean_processes'] for s in execution['resource_samples'])

    neighbours = [tuple(v ^ (1 << j) for j in range(9)) for v in range(512)]
    masks = [sum(1 << x for x in ns) for ns in neighbours]
    assert all((masks[z] >> v) & 1 for v in range(512) for z in neighbours[v])
    parity_classes = [[v for v in range(512) if v.bit_count() % 2 == c] for c in [0, 1]]
    totals = collections.Counter()
    candidates = []
    candidate_classes = {}
    base_counts = []
    completed_cores = 0
    descriptions = 0
    start = time.monotonic()
    status = 'RUNNING'
    mismatch = None
    try:
        for base in bases:
            original = sorted(base['vertices'])
            assert len(original) == len(set(original)) == 96
            assert all(0 <= v < 512 for v in original)
            parity = original[0].bit_count() % 2
            assert all(v.bit_count() % 2 == parity for v in original)
            original_set = set(original)
            original_mask = sum(1 << v for v in original)
            additions = [v for v in parity_classes[parity] if v not in original_set]
            assert len(additions) == 160
            counts_this_base = collections.Counter()
            for removed in original:
                if time.monotonic()-start >= args.seconds:
                    raise TimeoutError('Bounded audit ended before full coverage')
                core = [v for v in original if v != removed]
                core_mask = original_mask & ~(1 << removed)
                # Counts here choose only an evaluation order. Every decision
                # below uses fresh intersections with the actual full 96-set.
                core_degrees = [(mask & core_mask).bit_count() for mask in masks]
                priority = sorted(core, key=lambda v: (sum(core_degrees[z] <= 2 for z in neighbours[v]), v))
                expected_core = data['cores'][completed_cores]
                assert expected_core['core'] == completed_cores
                assert expected_core['base'] == base['id'] and expected_core['removed'] == removed
                local = collections.Counter()
                for ai, added in enumerate(additions):
                    ident = completed_cores*160 + ai
                    selected = core_mask | (1 << added)
                    assert selected.bit_count() == 96
                    actual = classify(selected, [added]+priority, neighbours, masks)
                    recorded = decisions[ident]
                    if actual != recorded:
                        mismatch = {'id': ident, 'base': base['id'], 'removed': removed, 'added': added,
                                    'recorded': CODES[recorded], 'reconstructed': CODES[actual]}
                        raise ValueError('Saved decision does not match direct reconstruction')
                    local[actual] += 1
                    totals[actual] += 1
                    counts_this_base[actual] += 1
                    descriptions += 1
                    if actual == 0:
                        candidates.append({'id': ident, 'base': base['id'], 'removed': removed, 'added': added})
                        candidate_classes.setdefault(selected, []).append(ident)
                assert {str(k): v for k, v in local.items()} == expected_core['statuses']
                completed_cores += 1
            base_counts.append({'base': base['id'], 'statuses': {CODES[k]: v for k, v in counts_this_base.items()}})
            progress = stdout[base['id']]
            assert progress['next_core'] == completed_cores
            assert progress['statuses'] == {CODES[k]: v for k, v in totals.items()}
            print(json.dumps({'completed_bases': len(base_counts), 'completed_cores': completed_cores,
                              'descriptions': descriptions, 'audit_seconds': time.monotonic()-start}), flush=True)
        assert completed_cores == 13920 and descriptions == 2227200
        assert candidates == data['candidates']
        assert {CODES[k]: v for k, v in totals.items()} == data['statuses']
        assert all(sha(path) == digest for path, digest in pins.items())
        status = 'PASS_FULL_INDEPENDENT_STATIC_DECISION_AUDIT'
    except TimeoutError as exc:
        status = 'PARTIAL_TIME_LIMIT'
        mismatch = {'reason': str(exc)}
    except Exception as exc:
        status = 'FAIL'
        mismatch = mismatch or {'type': type(exc).__name__, 'reason': str(exc)}

    output = {
        'status': status, 'scope': 'All labelled one-exchange descriptions; static necessary conditions only.',
        'pins': pins, 'auditor_sha256': sha(Path(__file__)),
        'completed_cores': completed_cores, 'verified_descriptions': descriptions,
        'statuses': {CODES[k]: v for k, v in totals.items()}, 'base_counts': base_counts,
        'verified_candidate_descriptions': len(candidates),
        'exact_distinct_candidate_classes': len(candidate_classes),
        'duplicate_candidate_groups': [ids for ids in candidate_classes.values() if len(ids)>1],
        'audit_seconds': time.monotonic()-start, 'failure_or_partial_reason': mismatch,
        'execution_receipt_status': execution['status'],
        'limitations': ['Candidate does not imply Hamiltonicity or an induced-path witness.',
                        'No Hamiltonian solver outcomes are audited by this script.',
                        'No full symmetry reduction or global Q9 bound is claimed.',
                        'This is direct finite reconstruction, not end-to-end Lean extraction.'],
    }
    destination.write_text(json.dumps(output, indent=2)+'\n', encoding='utf-8')
    with (H/'logs/exchange-audit.md').open('a', encoding='utf-8') as stream:
        stream.write('\n## Subsequent full decision-audit execution\n\n')
        stream.write(f'Status: `{status}`. Verified descriptions: {descriptions}; completed cores: {completed_cores}.\n\n')
        stream.write('Reconstructed counts: `'+json.dumps(output['statuses'], sort_keys=True)+'`.\n\n')
        stream.write(f'Verified candidate descriptions: {len(candidates)}; exact distinct candidate classes: {len(candidate_classes)}. Equality grouping uses the complete selected-vertex bit set only.\n\n')
        stream.write(f'Audit JSON SHA-256: `{sha(destination)}`. Auditor SHA-256: `{sha(Path(__file__))}`.\n\n')
        stream.write('No optimizer, compiler, or software test was invoked. The audit does not resolve Hamiltonicity of any surviving candidate.\n')
        if mismatch is not None:
            stream.write('\nIncomplete/failure detail: `'+json.dumps(mismatch, sort_keys=True)+'`.\n')
    print(json.dumps({k: output[k] for k in ['status', 'completed_cores', 'verified_descriptions',
                    'statuses', 'verified_candidate_descriptions', 'exact_distinct_candidate_classes',
                    'audit_seconds', 'failure_or_partial_reason']}, indent=2), flush=True)
    if status != 'PASS_FULL_INDEPENDENT_STATIC_DECISION_AUDIT':
        raise SystemExit(2)


if __name__ == '__main__':
    main()
