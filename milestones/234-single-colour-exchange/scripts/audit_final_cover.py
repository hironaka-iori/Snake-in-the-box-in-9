"""Audit saved candidate graphs, native models, replay pins, and union coverage.

No optimizer, compiler, or repeated forced-edge propagation is invoked.
Execute only after the separate full static audit has completed successfully.
Writes only the assigned Markdown review; prints a machine-readable summary.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import re
import time

H = Path(__file__).resolve().parents[1]
TRACKED = {}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()


def pin(path, expected=None):
    path = Path(path).resolve()
    value = sha(path)
    assert expected is None or expected == value, str(path)
    assert str(path) not in TRACKED or TRACKED[str(path)] == value
    TRACKED[str(path)] = value
    return value


def read(path):
    pin(path)
    return json.loads(Path(path).read_bytes())


def pins(mapping):
    for path, expected in mapping.items():
        pin(path, expected)


def canonical(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def execution(tag, result_path):
    record = read(H/'data'/(tag+'-execution.json'))
    assert record['status'] == 'ACCEPTED_NATIVE_RESULT'
    assert record['exit_code'] == 0 and record['stop_reason'] is None
    pins(record['pins'])
    pin(result_path, record['result_sha256'])
    for suffix in ['stdout', 'stderr']:
        pin(H/'logs'/(tag+'-'+suffix+'.log'), record[suffix+'_sha256'])
    assert not (H/'logs'/(tag+'-stderr.log')).read_bytes()
    assert all(not s['errors'] and not s['lean_processes'] for s in record['resource_samples'])
    return {'status': record['status'], 'seconds': record['seconds'],
            'samples': len(record['resource_samples']),
            'maximum_sampled_private_bytes': max(s['private_bytes'] or 0 for s in record['resource_samples'])}


def graph(vertices):
    assert len(vertices) == len(set(vertices)) == 96 and vertices == sorted(vertices)
    assert all(0 <= v < 512 for v in vertices)
    parity = vertices[0].bit_count() % 2
    assert all(v.bit_count() % 2 == parity for v in vertices)
    ports, labels = {}, {}
    adjacency = {v: set() for v in vertices}
    for z in range(512):
        if z.bit_count() % 2 == parity:
            continue
        neighbours = [v for v in vertices if (v ^ z).bit_count() == 1]
        if len(neighbours) == 1:
            ports.setdefault(neighbours[0], []).append(z)
        elif len(neighbours) == 2:
            a, b = neighbours
            labels.setdefault((a, b), []).append(z)
            adjacency[a].add(b)
            adjacency[b].add(a)
    assert len(ports) >= 2 and all(adjacency.values())
    leaves = [v for v in vertices if len(adjacency[v]) == 1]
    assert len(leaves) <= 2 and all(v in ports for v in leaves)
    reached = {vertices[0]}
    todo = [vertices[0]]
    while todo:
        v = todo.pop()
        for w in adjacency[v] - reached:
            reached.add(w)
            todo.append(w)
    assert reached == set(vertices)
    summary = {'vertices': vertices, 'ports': [[v, zs] for v, zs in sorted(ports.items())],
               'labelled_edges': [[a, b, zs] for (a, b), zs in sorted(labels.items())]}
    initial = {'graph_sha256': canonical(summary), 'vertices_with_dummy': 97,
               'available_edges': len(labels)+len(ports), 'endpoint_supported_vertices': len(ports),
               'internal_label_count': sum(map(len, labels.values()))}
    index = {v: i for i, v in enumerate(vertices)}
    arcs = []
    for a, b in labels:
        arcs.extend([(index[a], index[b]), (index[b], index[a])])
    for v in ports:
        arcs.extend([(index[v], 96), (96, index[v])])
    return ports, labels, leaves, initial, arcs


def model(path, expected):
    text = Path(path).read_text(encoding='utf-8')
    vp = r'variables\s*\{\s*name:\s*"a(\d+)_(\d+)"\s*domain:\s*\[0,\s*1\]\s*\}'
    assert [tuple(map(int, row)) for row in re.findall(vp, text)] == expected
    remaining = re.sub(vp, '', text).strip()
    cp = (r'constraints\s*\{\s*circuit\s*\{\s*tails:\s*\[([^\]]*)\]'
          r'\s*heads:\s*\[([^\]]*)\]\s*literals:\s*\[([^\]]*)\]\s*\}\s*\}')
    matched = re.fullmatch(cp, remaining)
    assert matched
    assert all(re.fullmatch(r'\s*-?\d+(?:,\s*-?\d+)*\s*', s) for s in matched.groups())
    arrays = [list(map(int, re.findall(r'-?\d+', s))) for s in matched.groups()]
    assert all(len(a) == len(expected) for a in arrays)
    assert list(zip(arrays[0], arrays[1])) == expected
    assert arrays[2] == list(range(len(expected)))
    assert len(set(expected)) == len(expected) and all(a != b for a, b in expected)
    assert set(v for edge in expected for v in edge) == set(range(97))


def main():
    if not __debug__:
        raise RuntimeError('This certificate audit requires Python assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--execute', required=True, action='store_true')
    parser.parse_args()
    start = time.monotonic()
    pin(Path(__file__))
    static = read(H/'data/exchange-audit.json')
    assert static['status'] == 'PASS_FULL_INDEPENDENT_STATIC_DECISION_AUDIT'
    assert static['completed_cores'] == 13920 and static['verified_descriptions'] == 2227200
    pins(static['pins'])
    pin(H/'scripts/audit_exchange.py', static['auditor_sha256'])
    executions = {'static_audit': execution('exchange-audit-verified', H/'data/exchange-audit.json')}
    source = read(H/'data/bases.json')
    exchange = read(H/'data/exchange.json')
    candidates = read(H/'data/candidates.json')
    pins(candidates['pins'])
    original = {b['id']: set(b['vertices']) for b in source['bases']}
    groups = {}
    for d in exchange['candidates']:
        selected = tuple(sorted((original[d['base']]-{d['removed']}) | {d['added']}))
        groups.setdefault(selected, []).append(d)
    assert len(exchange['candidates']) == static['verified_candidate_descriptions'] == 1381
    assert len(groups) == len(candidates['bases']) == static['exact_distinct_candidate_classes'] == 1325
    for ident, (row, (vertices, descriptions)) in enumerate(zip(candidates['bases'], groups.items())):
        assert row == {'id': ident, 'vertices': list(vertices), 'descriptions': descriptions}
    universe = set(range(1325))

    forced = read(H/'data/forced-cycles.json')
    replay = read(H/'data/forced-replay.json')
    pins(replay['input_pins'])
    pin(H/'data/candidates.json', forced['source_sha256'])
    pin(H/'scripts/forced_cycles.py', forced['script_sha256'])
    assert forced['status'] == 'COMPLETE_PROPAGATION' and forced['total'] == 1325
    assert replay['status'] == 'PASS_COMPLETE_REPLAY' and replay['verified_classes'] == 1325
    assert [r['id'] for r in forced['rows']] == list(range(1325))
    assert [r['id'] for r in replay['rows']] == list(range(1325))
    certified = {r['id'] for r in replay['rows'] if r['status'] == 'VERIFIED_CONTRADICTION'}
    assert certified == {r['id'] for r in forced['rows'] if r['status'] == 'CERTIFICATE'}
    assert len(certified) == forced['certified'] == replay['certified_classes'] == 1244
    assert replay['unresolved_classes'] == sorted(universe-certified)
    assert replay['all_candidate_classes_excluded'] is False
    assert collections.Counter(r['terminal']['kind'] for r in replay['rows'] if r['terminal']) == replay['terminal_counts']
    executions['forced_generation'] = execution('forced-cycles', H/'data/forced-cycles.json')

    first = read(H/'data/hamilton.json')
    second = read(H/'data/hamilton-resume.json')
    remaining = read(H/'data/remaining.json')
    pins(remaining['pins'])
    assert first['status'] == 'TIME_LIMIT' and first['witness'] is None
    assert second['status'] == 'COMPLETE_QUERY_BATCH' and second['witness'] is None
    assert [r['id'] for r in first['results']] == list(range(771))
    assert first['statuses'] == {'INFEASIBLE': 771}
    first_ids = {r['id'] for r in first['results']}
    assert remaining['bases'] == [b for b in candidates['bases'] if b['id'] not in certified | first_ids]
    assert len(remaining['bases']) == 22
    assert [r['id'] for r in second['results']] == [b['id'] for b in remaining['bases']]
    assert second['statuses'] == {'INFEASIBLE': 22}
    executions['first_native_batch'] = execution('hamilton', H/'data/hamilton.json')
    executions['remaining_native_batch'] = execution('hamilton-resume', H/'data/hamilton-resume.json')
    native = {}
    for result, source_name, script_name in [(first, 'candidates', 'hamilton'), (second, 'remaining', 'hamilton_resume')]:
        pin(H/'data'/(source_name+'.json'), result['source_sha256'])
        pin(H/'scripts'/(script_name+'.py'), result['script_sha256'])
        for row in result['results']:
            assert row['status'] == 'INFEASIBLE' and row['id'] not in native
            native[row['id']] = row
    assert len(native) == 793

    model_roster = []
    graph_roster = []
    for base, fr, rr in zip(candidates['bases'], forced['rows'], replay['rows']):
        ident = base['id']
        ports, labels, leaves, initial, arcs = graph(base['vertices'])
        assert rr['initial'] == initial
        assert rr['trace_sha256'] == canonical(fr['trace']) and rr['steps'] == len(fr['trace'])
        assert rr['operations'] == dict(collections.Counter(s[0] for s in fr['trace']))
        if ident in certified:
            assert rr['terminal'] is not None and fr['contradiction'] is not None
            assert all(rr['terminal'][key] == value for key, value in fr['contradiction'].items())
        else:
            assert rr['status'] == 'VALID_TRACE_UNRESOLVED'
            assert rr['terminal'] is None and fr['contradiction'] is None
        graph_roster.append([ident, initial['graph_sha256']])
        if ident not in native:
            continue
        row = native[ident]
        assert row['ports'] == {str(v): zs for v, zs in ports.items()}
        assert row['edges'] == [[a, b, z] for (a, b), zs in labels.items() for z in zs]
        assert row['leaves'] == leaves
        path = H/'data'/row['model']
        expected_name = f'hamilton-{ident:03d}.pbtxt' if ident in first_ids else f'hamilton-resume-{ident:03d}.pbtxt'
        assert path.name == expected_name
        digest = pin(path, row['model_sha256'])
        model(path, arcs)
        model_roster.append([ident, path.name, digest, len(arcs)])
    essential = universe-certified
    assert essential <= set(native) and len(essential) == 81
    assert certified | set(native) == universe
    assert len(model_roster) == 793
    assert all(sha(path) == digest for path, digest in TRACKED.items())
    output = {'status': 'PASS_COMPLETE_CANDIDATE_UNION_COVER',
              'candidate_descriptions': 1381, 'distinct_candidate_classes': 1325,
              'elementary_certified_classes': 1244, 'essential_native_classes': 81,
              'all_native_models_verified': 793, 'native_elementary_overlap': len(certified & set(native)),
              'initial_native_rows': 771, 'remaining_native_rows': 22,
              'unresolved_candidate_classes': [], 'essential_native_ids': sorted(essential),
              'graph_roster_sha256': canonical(graph_roster), 'model_roster_sha256': canonical(model_roster),
              'input_pins': TRACKED, 'executions': executions, 'audit_seconds': time.monotonic()-start,
              'scope': 'Full static-audit gate, exact deduplication, all1325 initial graphs, all793 native models, saved elementary replay pins and complete union cover.',
              'limitations': ['No solver rerun or native contradiction-certificate replay.',
                             'Forced-edge step replay was not duplicated; its existing complete receipt and source/input/trace pins were checked.',
                             'No end-to-end Lean graph extraction or global Q9 upper bound.']}
    with (H/'logs/final-cover-audit.md').open('a', encoding='utf-8') as stream:
        stream.write('\n## Executed final coverage audit\n\n')
        stream.write('Status: `PASS_COMPLETE_CANDIDATE_UNION_COVER`. The full independent static audit passed before this audit began. Exact grouping gives 1,325 classes from 1,381 candidate descriptions. All 1,325 graphs and all 793 exported native models match direct reconstruction.\n\n')
        stream.write('The pinned complete elementary replay excludes 1,244 classes. Exactly 81 remaining classes have verified native infeasibility models/results: 59 from the initial batch and 22 from the completion batch. Their union covers all 1,325 classes. The initial native batch remains correctly labelled TIME_LIMIT despite its 771 completed infeasibility results.\n\n')
        stream.write('The existing elementary step replay was not rerun; its source, input, individual trace, and reconstructed initial-graph pins were checked. The 81 essential native contradictions remain solver evidence. No optimizer, compiler, or software test was invoked.\n\n')
        stream.write(f"Graph roster SHA-256: `{output['graph_roster_sha256']}`. Model roster SHA-256: `{output['model_roster_sha256']}`. Auditor SHA-256: `{sha(Path(__file__))}`.\n\n")
        stream.write('Compact evidence pins (individual model hashes remain in the pinned native-result files):\n\n')
        for path, digest in TRACKED.items():
            if not path.endswith('.pbtxt'):
                stream.write(f'- `{path}`: `{digest}`\n')
    # The parent wrapper may preserve this stdout as its machine-readable receipt.
    print(json.dumps(output, indent=2), flush=True)


if __name__ == '__main__':
    main()
