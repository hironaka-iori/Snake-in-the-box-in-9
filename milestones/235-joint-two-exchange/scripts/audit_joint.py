"""Read-only audit of saved joint-exchange models and terminal native records.

No solver, compiler, producer import, or software test is invoked. The JSON
receipt is printed to stdout; the parent may preserve it separately.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import itertools
import json
import re
import time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
PINS = {}
LOW, HIGH = -(1 << 63), (1 << 63)-1


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()


def pin(path, expected=None):
    path = str(Path(path).resolve())
    value = sha(path)
    assert expected is None or value == expected, path
    assert path not in PINS or PINS[path] == value
    PINS[path] = value
    return value


def read(path):
    pin(path)
    return json.loads(Path(path).read_bytes())


def check_pins(mapping):
    for path, value in mapping.items():
        pin(path, value)


def arrays(body, keys):
    pattern = r'([a-z_]+)\s*:\s*\[([^\]]*)\]'
    found = re.findall(pattern, body)
    assert not re.sub(pattern, '', body).strip()
    assert len(found) == len(keys) and {k for k, _ in found} == set(keys)
    result = {}
    for key, contents in found:
        assert re.fullmatch(r'\s*-?\d+(?:\s*,\s*-?\d+)*\s*', contents)
        result[key] = list(map(int, re.findall(r'-?\d+', contents)))
    return result


def normalized(terms, domain):
    return tuple(sorted((name, coefficient) for name, coefficient in terms if coefficient)), tuple(domain)


def inspect_model(path, vertices, exchanges):
    text = path.read_text(encoding='utf-8')
    vp = r'variables\s*\{\s*name:\s*"([^"\n]+)"\s*domain:\s*\[0,\s*1\]\s*\}'
    names = re.findall(vp, text)
    assert len(names) == len(set(names)) == 5632
    rest = re.sub(vp, '', text)
    cp = r'constraints\s*\{\s*(linear|circuit)\s*\{([^{}]*)\}\s*\}'
    constraints = re.findall(cp, rest)
    assert not re.sub(cp, '', rest).strip()
    assert len(constraints) == 7428
    parity = vertices[0].bit_count() % 2
    minor = [v for v in range(512) if v.bit_count() % 2 == parity]
    major = sorted(set(range(512))-set(minor))
    # Independent edge enumeration uses all unordered pairs and Hamming distance.
    edges = [(v, w) for v, w in itertools.combinations(range(512), 2)
             if (v ^ w).bit_count() == 1]
    assert len(edges) == 2304
    expected_names = {f'x{v}' for v in range(512)}
    expected_names |= {f'a{a}_{b}' for v, w in edges for a, b in [(v, w), (w, v)]}
    expected_names |= {f'{kind}{v}' for kind in ['s', 't'] for v in major}
    assert set(names) == expected_names
    expected = collections.Counter()
    for v, w in edges:
        f, b = f'a{v}_{w}', f'a{w}_{v}'
        for u in [v, w]:
            expected[normalized([(f, 1), (b, 1), (f'x{u}', -1)], [LOW, 0])] += 1
        expected[normalized([(f, 1), (b, 1), (f'x{v}', -1), (f'x{w}', -1)], [-1, HIGH])] += 1
    for v in major:
        for kind in ['s', 't']:
            expected[normalized([(f'{kind}{v}', 1), (f'x{v}', -1)], [LOW, 0])] += 1
    for group, target in [(minor, 96), (major, 97), (vertices, 96-exchanges)]:
        expected[normalized([(f'x{v}', 1) for v in group], [target, target])] += 1
    actual = collections.Counter()
    circuits = []
    for kind, body in constraints:
        if kind == 'circuit':
            circuits.append(arrays(body, ['tails', 'heads', 'literals']))
            continue
        row = arrays(body, ['vars', 'coeffs', 'domain'])
        assert len(row['vars']) == len(row['coeffs'])
        assert len(row['vars']) == len(set(row['vars']))
        assert all(0 <= i < len(names) for i in row['vars'])
        assert len(row['domain']) == 2
        actual[normalized([(names[i], c) for i, c in zip(row['vars'], row['coeffs'])], row['domain'])] += 1
    assert actual == expected and sum(actual.values()) == 7427
    assert len(circuits) == 1
    circuit = circuits[0]
    assert all(len(a) == 5632 for a in circuit.values())
    triples = []
    for tail, head, literal in zip(circuit['tails'], circuit['heads'], circuit['literals']):
        index = literal if literal >= 0 else -literal-1
        assert 0 <= index < len(names)
        triples.append((tail, head, ('!' if literal < 0 else '')+names[index]))
    expected_triples = {(v, v, f'!x{v}') for v in range(512)}
    expected_triples |= {(a, b, f'a{a}_{b}') for v, w in edges for a, b in [(v, w), (w, v)]}
    expected_triples |= {(512, v, f's{v}') for v in major}
    expected_triples |= {(v, 512, f't{v}') for v in major}
    assert len(triples) == len(set(triples)) and set(triples) == expected_triples
    return {'variables': len(names), 'constraints': len(constraints), 'cube_edges': len(edges),
            'linear_constraints': sum(actual.values()), 'circuit_arcs': len(triples),
            'minority_parity': parity, 'retained_saved_vertices': 96-exchanges}


def inspect_witness(witness, base, exchanges):
    path = witness['path']
    assert witness['base'] == base['id'] and witness['edges'] == 192
    assert len(path) == len(set(path)) == 193 and all(0 <= v < 512 for v in path)
    for i, v in enumerate(path):
        for j in range(i+1, len(path)):
            assert ((v ^ path[j]).bit_count() == 1) == (j == i+1)
    old = set(base['vertices'])
    parity = base['vertices'][0].bit_count() % 2
    minor = {v for v in path if v.bit_count() % 2 == parity}
    assert len(minor) == 96 and len(set(path)-minor) == 97
    assert path[0] not in minor and path[-1] not in minor
    assert witness['minority_class'] == sorted(minor)
    assert witness['removed'] == sorted(old-minor) and witness['inserted'] == sorted(minor-old)
    assert len(old-minor) == len(minor-old) == exchanges
    return {'edges': 192, 'vertices': 193, 'all_pairs_checked': 18528, 'exchanges': exchanges}


def main():
    if not __debug__:
        raise RuntimeError('The audit requires Python assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--execute', action='store_true', required=True)
    parser.add_argument('--tag', default='joint')
    args = parser.parse_args()
    assert re.fullmatch(r'[a-zA-Z0-9_-]+', args.tag)
    assert not (H/'data/forest-search.lock').exists(), 'Wait for the native worker to finish.'
    started = time.monotonic()
    pin(Path(__file__))
    for name in ['joint_search.py', 'run_joint.py', 'prepare_round.py', 'native_resources.py']:
        pin(H/'scripts'/name)
    pin(H.parent/'199-parent-diversity/scripts/circuit_search.py')
    pin(R/'work/solver_packages/ortools/sat/python/cp_model.py')
    bases = read(H/'data/bases.json')
    check_pins(bases['pins'])
    assert [b['id'] for b in bases['bases']] == list(range(145))
    for base in bases['bases']:
        v = base['vertices']
        assert v == sorted(set(v)) and len(v) == 96 and all(0 <= x < 512 for x in v)
        assert len({x.bit_count() % 2 for x in v}) == 1
    result = read(H/'data'/(args.tag+'.json'))
    execution = read(H/'data'/(args.tag+'-execution.json'))
    assert execution['status'] == 'ACCEPTED_NATIVE_RESULT'
    assert execution['exit_code'] == 0 and execution['stop_reason'] is None
    check_pins(execution['pins'])
    pin(H/'data'/(args.tag+'.json'), execution['result_sha256'])
    pin(H/'data/bases.json', result['source_sha256'])
    pin(H/'scripts/joint_search.py', result['script_sha256'])
    for suffix in ['stdout', 'stderr']:
        pin(H/'logs'/(args.tag+'-'+suffix+'.log'), execution[suffix+'_sha256'])
    assert not (H/'logs'/(args.tag+'-stderr.log')).read_bytes()
    assert all(not s['errors'] and not s['lean_processes'] for s in execution['resource_samples'])
    requested = [int(i) for i in result['arguments']['bases'].split(',')]
    assert len(requested) == len(set(requested)) and all(0 <= i < 145 for i in requested)
    exchanges = result['arguments']['exchanges']
    assert 0 <= exchanges <= 96 and result['arguments']['tag'] == args.tag
    assert [r['base'] for r in result['results']] == requested[:len(result['results'])]
    rows = []
    witness_record = None
    for row in result['results']:
        assert row['status'] in ['UNKNOWN', 'INFEASIBLE', 'WITNESS'], row['status']
        assert row['exchanges'] == exchanges
        name = f'{args.tag}-{row["base"]:03d}.pbtxt'
        assert row['model'] == name
        path = H/'data'/name
        pin(path, row['model_sha256'])
        details = inspect_model(path, bases['bases'][row['base']]['vertices'], exchanges)
        assert row['variables'] == details['variables'] and row['constraints'] == details['constraints']
        response = re.search(r'^status: (\w+)\s*$', row['response_stats'], re.MULTILINE)
        assert response
        if row['status'] == 'WITNESS':
            assert response.group(1) in ['FEASIBLE', 'OPTIMAL']
            assert witness_record is None and row == result['results'][-1]
            witness_record = inspect_witness(result['witness'], bases['bases'][row['base']], exchanges)
        else:
            assert response.group(1) == row['status']
        rows.append({'base': row['base'], 'status': row['status'], 'model': name,
                     'model_sha256': row['model_sha256'], 'seconds': row['seconds'], **details})
    if witness_record is not None:
        assert result['status'] == 'WITNESS'
    else:
        assert result['witness'] is None
        assert result['status'] == ('COMPLETE_QUERY_BATCH' if len(rows) == len(requested) else 'TIME_LIMIT')
    stdout = [json.loads(line) for line in (H/'logs'/(args.tag+'-stdout.log')).read_text().splitlines() if line.strip()]
    expected_stdout = [{k: row[k] for k in ['base', 'status', 'seconds', 'branches', 'conflicts']}
                       for row in result['results'] if row['status'] != 'WITNESS']
    expected_stdout.append({'status': result['status'],
                            'results': [{k: row[k] for k in ['base', 'status']} for row in result['results']],
                            'witness': result['witness']})
    assert stdout == expected_stdout
    assert all(sha(path) == value for path, value in PINS.items())
    output = {'status': 'PASS_SAVED_JOINT_MODEL_AUDIT', 'batch_status': result['status'],
              'requested_bases': requested, 'exchanges': exchanges, 'rows': rows,
              'statuses': dict(collections.Counter(r['status'] for r in rows)),
              'unqueried_bases': requested[len(rows):], 'witness': witness_record,
              'maximum_sampled_private_bytes': max(s['private_bytes'] or 0 for s in execution['resource_samples']),
              'wrapper_seconds': execution['seconds'], 'audit_seconds': time.monotonic()-started,
              'source_and_input_pins': PINS,
              'scope': 'Exact saved models for the requested base classes; no solver rerun or global coverage.',
              'limits': ['UNKNOWN remains unresolved.', 'Native INFEASIBLE is not a replayed contradiction certificate.',
                         'No end-to-end Lean assembly or complete two-exchange census is established.']}
    with (H/'logs/model-review.md').open('a', encoding='utf-8') as stream:
        stream.write('\n## Saved-model audit execution\n\n')
        stream.write(f"Status: `{output['status']}`. Inspected {len(rows)} complete exported models, each with 5,632 Boolean variables, 7,427 exact linear constraints and one circuit constraint. Native statuses: `{output['statuses']}`. Batch status remains `{result['status']}`.\n\n")
        stream.write(f"Verified witness: `{witness_record}`. Unqueried requested bases: `{output['unqueried_bases']}`. Unknown results remain unresolved. No native contradiction was independently replayed.\n\n")
        stream.write(f"Auditor SHA-256: `{sha(Path(__file__))}`. Full source/model/log pins are in the JSON stdout receipt.\n")
    print(json.dumps(output, indent=2), flush=True)


if __name__ == '__main__':
    main()
