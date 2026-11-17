"""Audit frozen degree-relaxation models and recorded native outcomes.

This script reconstructs exact constraints and any feasible components/cycle
cuts. It never invokes a solver, compiler, producer, or software test.
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
PINS = {}
LOW = -(1 << 63)
NEIGHBOURS = {v: {w for w in range(512) if (v ^ w).bit_count() == 1} for v in range(512)}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()


def pin(path, expected=None):
    path = str(Path(path).resolve())
    value = sha(path)
    assert expected is None or expected == value, path
    assert path not in PINS or PINS[path] == value
    PINS[path] = value
    return value


def read(path):
    pin(path)
    return json.loads(Path(path).read_bytes())


def pins(mapping):
    for path, value in mapping.items():
        pin(path, value)


def integer_array(contents):
    assert re.fullmatch(r'\s*-?\d+(?:\s*,\s*-?\d+)*\s*', contents)
    return list(map(int, re.findall(r'-?\d+', contents)))


def normalized(terms, domain, guard=None):
    return tuple(sorted(terms)), tuple(domain), guard


def expected_model(base, exchanges, cuts):
    parity = base['vertices'][0].bit_count() % 2
    minor = {v for v in range(512) if v.bit_count() % 2 == parity}
    major = set(range(512))-minor
    expected = collections.Counter()
    for group, value in [(minor, 96), (major, 97), (base['vertices'], 96-exchanges)]:
        expected[normalized([(f'x{v}', 1) for v in group], [value, value])] += 1
    expected[normalized([(f'e{v}', 1) for v in major], [2, 2])] += 1
    for v in major:
        expected[normalized([(f'e{v}', 1), (f'x{v}', -1)], [LOW, 0])] += 1
    for v in range(512):
        terms = [(f'x{w}', 1) for w in NEIGHBOURS[v]]
        if v in major:
            terms.append((f'e{v}', 1))
        expected[normalized(terms, [2, 2], f'x{v}')] += 1
    for cut in cuts:
        expected[normalized([(f'x{v}', 1) for v in cut], [LOW, len(cut)-1])] += 1
    return expected, minor, major


def inspect_model(path, base, exchanges, cuts):
    text = path.read_text(encoding='utf-8')
    vp = r'variables\s*\{\s*name:\s*"([^"\n]+)"\s*domain:\s*\[0,\s*1\]\s*\}'
    names = re.findall(vp, text)
    expected, minor, major = expected_model(base, exchanges, cuts)
    assert len(names) == len(set(names)) == 768
    assert set(names) == {f'x{v}' for v in range(512)} | {f'e{v}' for v in major}
    rest = re.sub(vp, '', text)
    cp = (r'constraints\s*\{\s*(?:enforcement_literal:\s*\[([^\]]*)\]\s*)?'
          r'linear\s*\{([^{}]*)\}\s*\}')
    rows = re.findall(cp, rest)
    assert not re.sub(cp, '', rest).strip()
    assert len(rows) == 772+len(cuts)
    actual = collections.Counter()
    guarded = 0
    for guard, body in rows:
        fields = re.findall(r'(vars|coeffs|domain):\s*\[([^\]]*)\]', body)
        assert not re.sub(r'(vars|coeffs|domain):\s*\[([^\]]*)\]', '', body).strip()
        assert len(fields) == 3 and {key for key, _ in fields} == {'vars', 'coeffs', 'domain'}
        fields = {key: integer_array(value) for key, value in fields}
        assert len(fields['vars']) == len(fields['coeffs'])
        assert len(fields['vars']) == len(set(fields['vars']))
        assert all(0 <= i < len(names) for i in fields['vars'])
        assert len(fields['domain']) == 2
        guarding_name = None
        if guard:
            literals = integer_array(guard)
            assert len(literals) == 1 and 0 <= literals[0] < len(names)
            guarding_name = names[literals[0]]
            assert guarding_name.startswith('x')
            guarded += 1
        actual[normalized([(names[i], c) for i, c in zip(fields['vars'], fields['coeffs'])],
                          fields['domain'], guarding_name)] += 1
    assert guarded == 512 and actual == expected
    return {'variables': len(names), 'constraints': len(rows), 'positive_selection_guards': guarded,
            'unconditional_constraints': len(rows)-guarded, 'cycle_cuts': len(cuts)}


def components(selected):
    todo = set(selected)
    result = []
    while todo:
        component = {min(todo)}
        queue = list(component)
        while queue:
            v = queue.pop()
            fresh = (NEIGHBOURS[v] & selected)-component
            component |= fresh
            queue.extend(fresh)
        todo -= component
        result.append(component)
    return result


def inspect_selection(step, base, exchanges, previous_cuts):
    selected = step['selected']
    ends = step['endpoints']
    assert selected == sorted(set(selected)) and len(selected) == 193
    assert ends == sorted(set(ends)) and len(ends) == 2
    assert all(isinstance(v, int) and 0 <= v < 512 for v in selected)
    selected, ends = set(selected), set(ends)
    old = set(base['vertices'])
    parity = base['vertices'][0].bit_count() % 2
    minor = {v for v in selected if v.bit_count() % 2 == parity}
    assert len(minor) == 96 and len(selected-minor) == 97
    assert ends <= selected-minor
    assert len(old-minor) == len(minor-old) == exchanges
    assert all(len(NEIGHBOURS[v] & selected) == 2-int(v in ends) for v in selected)
    assert all(not set(cut) <= selected for cut in previous_cuts)
    groups = components(selected)
    assert sorted(map(len, groups)) == step['component_sizes']
    paths = [group for group in groups if group & ends]
    assert len(paths) == 1 and ends <= paths[0]
    cycles = [group for group in groups if not group & ends]
    for cycle in cycles:
        assert len(cycle) >= 4 and len(cycle) % 2 == 0
        assert all(len(NEIGHBOURS[v] & cycle) == 2 for v in cycle)
    return [sorted(cycle) for cycle in cycles]


def inspect_witness(witness, base, exchanges, selected):
    path = witness['path']
    assert witness['base'] == base['id'] and witness['edges'] == 192
    assert len(path) == len(set(path)) == 193 and set(path) == set(selected)
    assert all(((path[i] ^ path[j]).bit_count() == 1) == (j == i+1)
               for i, j in itertools.combinations(range(193), 2))
    parity = base['vertices'][0].bit_count() % 2
    minority = {v for v in path if v.bit_count() % 2 == parity}
    old = set(base['vertices'])
    assert len(minority) == 96 and path[0] not in minority and path[-1] not in minority
    assert witness['minority_class'] == sorted(minority)
    assert witness['removed'] == sorted(old-minority) and witness['inserted'] == sorted(minority-old)
    assert len(old-minority) == len(minority-old) == exchanges


def audit_batch(tag, bases):
    result = read(H/'data'/(tag+'.json'))
    execution = read(H/'data'/(tag+'-execution.json'))
    assert execution['status'] == 'ACCEPTED_NATIVE_RESULT' and execution['exit_code'] == 0
    assert execution['stop_reason'] is None
    pins(execution['pins'])
    pin(H/'data'/(tag+'.json'), execution['result_sha256'])
    pin(H/'scripts/degree_search.py', result['script_sha256'])
    pin(H/'data/bases.json', result['source_sha256'])
    for suffix in ['stdout', 'stderr']:
        pin(H/'logs'/(tag+'-'+suffix+'.log'), execution[suffix+'_sha256'])
    assert not (H/'logs'/(tag+'-stderr.log')).read_bytes()
    assert all(not s['errors'] and not s['lean_processes'] for s in execution['resource_samples'])
    arguments = result['arguments']
    assert arguments['tag'] == tag and arguments['exchanges'] == 2
    requested = [int(v) for v in arguments['bases'].split(',')]
    assert len(requested) == len(set(requested)) and all(0 <= v < 145 for v in requested)
    assert [row['base'] for row in result['results']] == requested[:len(result['results'])]
    reviewed = []
    witness_count = 0
    for row in result['results']:
        base = bases[row['base']]
        assert row['exchanges'] == 2
        assert row['status'] in ['INFEASIBLE', 'UNKNOWN', 'TIME_LIMIT', 'WITNESS']
        prior_cuts = []
        reconstructed_cuts = []
        models = []
        assert [step['iteration'] for step in row['iterations']] == list(range(len(row['iterations'])))
        for step in row['iterations']:
            i = step['iteration']
            assert step['status'] in ['INFEASIBLE', 'UNKNOWN', 'FEASIBLE', 'OPTIMAL']
            assert step['cut_count_before'] == len(prior_cuts)
            name = f'{tag}-{row["base"]:03d}-{i:04d}.pbtxt'
            assert step['model'] == name
            path = H/'data'/name
            pin(path, step['model_sha256'])
            details = inspect_model(path, base, 2, prior_cuts)
            models.append({'iteration': i, 'status': step['status'], 'model': name,
                           'sha256': step['model_sha256'], **details})
            if step['status'] in ['INFEASIBLE', 'UNKNOWN']:
                assert step == row['iterations'][-1] and row['status'] == step['status']
                assert not any(key in step for key in ['selected', 'endpoints', 'component_sizes'])
                continue
            cycles = inspect_selection(step, base, 2, prior_cuts)
            if not cycles:
                assert row['status'] == 'WITNESS' and step == row['iterations'][-1]
                assert row == result['results'][-1]
                inspect_witness(result['witness'], base, 2, step['selected'])
                witness_count += 1
            for cycle in cycles:
                assert cycle not in prior_cuts
                prior_cuts.append(cycle)
                reconstructed_cuts.append({'vertices': cycle, 'from_iteration': i})
        assert reconstructed_cuts == row['cuts']
        if row['status'] == 'TIME_LIMIT':
            assert not row['iterations'] or row['iterations'][-1]['status'] in ['FEASIBLE', 'OPTIMAL']
        elif row['status'] != 'WITNESS':
            assert row['iterations'] and row['iterations'][-1]['status'] == row['status']
        reviewed.append({'base': row['base'], 'status': row['status'], 'models': models,
                         'cycle_cuts': len(prior_cuts), 'seconds': row['seconds']})
    if witness_count:
        assert witness_count == 1 and result['status'] == 'WITNESS'
    else:
        assert result['witness'] is None
        assert result['status'] == ('COMPLETE_QUERY_BATCH' if len(reviewed) == len(requested) else 'TIME_LIMIT')
    stdout = [json.loads(line) for line in (H/'logs'/(tag+'-stdout.log')).read_text().splitlines() if line.strip()]
    expected_stdout = [{'base': row['base'], 'status': row['status'], 'queries': len(row['iterations']),
                        'cuts': len(row['cuts']), 'seconds': row['seconds']} for row in result['results']]
    expected_stdout.append({'status': result['status'],
                            'results': [{k: row[k] for k in ['base', 'status']} for row in result['results']],
                            'witness': result['witness']})
    assert stdout == expected_stdout
    return {'tag': tag, 'status': result['status'], 'requested': requested, 'rows': reviewed,
            'maximum_sampled_private_bytes': max(s['private_bytes'] or 0 for s in execution['resource_samples']),
            'wrapper_seconds': execution['seconds'], 'witness_count': witness_count}


def main():
    if not __debug__:
        raise RuntimeError('The certificate audit requires Python assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--execute', action='store_true', required=True)
    parser.add_argument('--tags', default='degree,degree-rest')
    parser.add_argument('--require-all-145', action='store_true')
    args = parser.parse_args()
    tags = args.tags.split(',')
    assert len(tags) == len(set(tags)) and all(re.fullmatch(r'[A-Za-z0-9_-]+', tag) for tag in tags)
    assert not (H/'data/forest-search.lock').exists(), 'Wait for the native worker to finish.'
    output_path = H/'data/degree-audit.json'
    assert not output_path.exists(), 'Preserve the existing audit receipt.'
    started = time.monotonic()
    for path in [Path(__file__), H/'scripts/degree_search.py', H/'scripts/run_degree.py']:
        pin(path)
    bases = read(H/'data/bases.json')
    pins(bases['pins'])
    assert [base['id'] for base in bases['bases']] == list(range(145))
    for base in bases['bases']:
        vertices = base['vertices']
        assert vertices == sorted(set(vertices)) and len(vertices) == 96
        assert all(0 <= v < 512 for v in vertices) and len({v.bit_count() % 2 for v in vertices}) == 1
    batches = [audit_batch(tag, bases['bases']) for tag in tags]
    rows = [row for batch in batches for row in batch['rows']]
    assert len(rows) == len({row['base'] for row in rows})
    covered = {row['base'] for row in rows}
    if args.require_all_145:
        assert covered == set(range(145))
    assert all(sha(path) == digest for path, digest in PINS.items())
    statuses = dict(collections.Counter(row['status'] for row in rows))
    output = {'status': 'PASS_DEGREE_MODEL_AUDIT', 'batches': batches, 'statuses': statuses,
              'covered_bases': sorted(covered), 'unqueried_bases': sorted(set(range(145))-covered),
              'models_verified': sum(len(row['models']) for row in rows),
              'cycle_cuts_verified': sum(row['cycle_cuts'] for row in rows),
              'all_145_native_excluded': statuses == {'INFEASIBLE': 145},
              'source_and_input_pins': PINS, 'audit_seconds': time.monotonic()-started,
              'scope': 'Exact degree-relaxation models for two minority replacements of saved classes.',
              'limitations': ['Native infeasibility is not an independently replayed contradiction.',
                             'Feasible disconnected selections are not snake witnesses.',
                             'No global Q9 bound or complete unrestricted construction search.']}
    output_path.write_text(json.dumps(output, indent=2)+'\n', encoding='utf-8')
    with (H/'logs/degree-model-review.md').open('a', encoding='utf-8') as stream:
        stream.write('\n## Executed saved-model audit\n\n')
        stream.write(f"Status `{output['status']}`. Covered {len(covered)} saved bases and checked {output['models_verified']} exported models. Native statuses: `{statuses}`. Verified added cycle cuts: {output['cycle_cuts_verified']}.\n\n")
        stream.write(f"All 145 saved exact-two-exchange families have native exclusions: `{output['all_145_native_excluded']}`. Unqueried bases: `{output['unqueried_bases']}`. This records native evidence and exact model inspection, without independent native contradiction replay.\n\n")
        stream.write(f"Auditor SHA-256: `{sha(Path(__file__))}`. Receipt SHA-256: `{sha(output_path)}`. Complete evidence pins are in `data/degree-audit.json`.\n")
    print(json.dumps({k: output[k] for k in ['status', 'statuses', 'models_verified', 'cycle_cuts_verified',
                                          'all_145_native_excluded', 'unqueried_bases', 'audit_seconds']}, indent=2))


if __name__ == '__main__':
    main()
