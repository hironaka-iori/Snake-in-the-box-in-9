"""Independently audit saved long-cycle rows and exact upper certificates.

This reads immutable evidence and performs integer/rational arithmetic only.
It does not import a producer, invoke an optimizer, or compile anything.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import math

HOME = Path(__file__).resolve().parents[1]
SQUARE_AUDIT_HASH = 'cc4c44f77167f7daa681d03de7ab28c2714f2c60307945511ff078353e534993'
MODEL_HASHES = {
    0: 'a4f0aa53fe7a8c06969643cd7a5b09c50459d6d5013e6568708b42a8ad76ce67',
    78: 'd0151302ca6cc914f5331befb72dcd00f22e9c0b06c46cc25da8efa8e8896dd3',
}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_bytes())


def pair(value):
    return [value.numerator, value.denominator]


def rational(value):
    assert len(value) == 2 and all(type(x) is int for x in value)
    assert value[1] > 0
    result = Fraction(*value)
    assert pair(result) == value
    return result


def pins(paths):
    return {str(p.relative_to(HOME)): digest(p) for p in paths}


def audit_execution():
    path = HOME / 'data/long-execution.json'
    execution = read(path)
    assert execution['status'] == 'ACCEPTED_NATIVE_RESULT'
    assert execution['exit_code'] == 0 and execution['stop_reason'] is None
    for name, expected in execution['pins'].items():
        assert digest(HOME / name) == expected, name
    for stream in ('stdout', 'stderr'):
        assert digest(HOME / f'logs/long-{stream}.log') == execution[f'{stream}_sha256']
    assert digest(HOME / 'data/long-summary.json') == execution['summary_sha256']
    assert execution['thread_environment'] == dict.fromkeys(
        ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'), '1')
    assert not execution['resource_gate']['errors']
    assert not execution['resource_gate']['processes']
    for sample in execution['resource_samples']:
        assert not sample['errors'] and not sample['lean_processes']
    return {
        'exit_code': 0, 'stop_reason': None, 'seconds': execution['seconds'],
        'receipt_sha256': digest(path), 'summary_sha256': execution['summary_sha256'],
        'peak_sampled_private_bytes': max(s['private_bytes'] or 0 for s in execution['resource_samples']),
        'minimum_sampled_free_bytes': min(s['free_bytes'] for s in execution['resource_samples']),
    }


def main():
    prior_path = HOME / 'data/square-audit.json'
    assert digest(prior_path) == SQUARE_AUDIT_HASH
    prior = read(prior_path)
    assert prior['status'] == 'PASS_EXACT_SQUARE_SUBSET_ROWS_AND_UPPER_CERTIFICATES'
    for name, expected in prior['pins'].items():
        assert digest(name) == expected, name
    execution = audit_execution()
    summary = read(HOME / 'data/long-summary.json')
    assert [entry['root'] for entry in summary] == [0, 78]
    reports = []
    for root in (0, 78):
        folder = HOME / f'data/long-{root}'
        model_path = folder / 'model.json'
        assert digest(model_path) == MODEL_HASHES[root]
        model = read(model_path)
        base_path = HOME / f'data/square-{root}/model.json'
        base = read(base_path)
        previous = next(item for item in prior['models'] if item['root'] == root)
        for name, expected in previous['pins'].items():
            assert digest(HOME / name) == expected, name
        assert model['base_model_sha256'] == digest(base_path)
        assert model['source_sha256_221'] == digest(HOME / 'scripts/long_separation.py')
        for key in ('root', 'form', 'variables', 'lower', 'upper', 'objective',
                    'vertices', 'edges', 'cycles', 'source_sha256', 'source_sha256_220',
                    'seed_sha256', 'graph_sha256', 'square_witnesses'):
            assert model[key] == base[key], key
        old_rows = len(base['rows'])
        assert model['rows'][:old_rows] == base['rows']
        old_subsets = len(base['subset_witnesses'])
        assert model['subset_witnesses'][:old_subsets] == base['subset_witnesses']
        vertices = model['vertices']
        assert vertices == sorted(set(vertices)) and len(vertices) == 158
        edges = [tuple(edge) for edge in model['edges']]
        edge_set = set(edges)
        expected_edges = {(u, v) for u in vertices for v in vertices
                          if u < v and (u ^ v).bit_count() == 1}
        assert len(edges) == len(edge_set) == 337 and edge_set == expected_edges
        variables = model['variables']
        assert len(variables) == len(set(variables)) == 574
        index = {name: i for i, name in enumerate(variables)}
        assert model['lower'] == [0] * 574 and model['upper'] == [1] * 574
        assert model['objective'] == [int(name.startswith('x')) for name in variables]
        covered = set()
        parity_records = []
        signed_edge_patterns = set()
        for k, witness in enumerate(model['cut_parity_witnesses']):
            cycle = witness['cycle']
            size = len(cycle)
            assert size >= 4 and size % 2 == 0 and size == len(set(cycle))
            assert set(cycle) <= set(vertices)
            cycle_edges = [tuple(sorted((a, b)))
                           for a, b in zip(cycle, cycle[1:] + cycle[:1])]
            assert len(set(cycle_edges)) == size and set(cycle_edges) <= edge_set
            odd = witness['odd_edge_indices']
            assert odd == sorted(set(odd)) and set(odd) <= set(range(size))
            assert len(odd) % 2 == 1
            signs = [1 if i in odd else -1 for i in range(size)]
            pattern = tuple(sorted(zip(cycle_edges, signs)))
            assert pattern not in signed_edge_patterns
            signed_edge_patterns.add(pattern)
            coefficients = Counter()
            for (u, v), sign in zip(cycle_edges, signs):
                coefficients[f'x{u}'] += sign
                coefficients[f'x{v}'] += sign
                coefficients[f'y{u}_{v}'] -= 2 * sign
            terms = sorted([index[name], a] for name, a in coefficients.items() if a)
            expected_row = {'name': f'cut_parity221_{k}', 'terms': terms,
                            'sense': 'le', 'rhs': len(odd) - 1}
            row_index = witness['row_index']
            assert row_index >= old_rows and row_index not in covered
            covered.add(row_index)
            assert model['rows'][row_index] == expected_row
            assert type(witness['iteration']) is int and witness['iteration'] >= 0
            assert math.isfinite(witness['violation_at_discovery'])
            assert witness['violation_at_discovery'] > 0
            parity_records.append({'row_index': row_index, 'cycle_length': size,
                                   'odd_subset_size': len(odd), 'row_reconstructed': True})
        new_subsets = model['subset_witnesses'][old_subsets:]
        subset_records = []
        for k, witness in enumerate(new_subsets):
            subset = witness['subset']
            selected = set(subset)
            marked = witness['vertex']
            assert subset == sorted(selected) and selected <= set(vertices) and marked in selected
            coefficients = {f'x{u}': -1 for u in subset if u != marked}
            coefficients.update({f'y{u}_{v}': 1 for u, v in edges if {u, v} <= selected})
            terms = sorted([index[name], a] for name, a in coefficients.items())
            expected_row = {'name': f'long_forest221_{k}', 'terms': terms, 'sense': 'le', 'rhs': 0}
            row_index = witness['row_index']
            assert row_index >= old_rows and row_index not in covered
            covered.add(row_index)
            assert model['rows'][row_index] == expected_row
            assert all((marked, subset) != (w['vertex'], w['subset'])
                       for w in base['subset_witnesses'])
            subset_records.append({'row_index': row_index, 'vertex': marked,
                                   'subset': subset, 'row_reconstructed': True})
        assert covered == set(range(old_rows, len(model['rows'])))
        assert len(parity_records) == (27 if root == 0 else 8)
        assert len(subset_records) == (0 if root == 0 else 1)
        native = read(folder / 'native-result.json')
        certificate = read(folder / 'upper-certificate.json')
        assert native['model_sha256'] == certificate['model_sha256'] == digest(model_path)
        assert native['status'] == 'OPTIMAL_NATIVE'
        assert native['added_parity_cycles'] == len(parity_records)
        assert native['added_subset_count'] == len(subset_records)
        assert native['inherited_square_rows'] == len(base['square_witnesses'])
        assert len(native['values']) == 574 and len(native['duals']) == len(model['rows'])
        assert all(math.isfinite(x) for x in native['values'] + native['duals'])
        assert next(x for x in summary if x['root'] == root) == {
            k: v for k, v in native.items() if k not in ('values', 'duals', 'steps')}
        weights = certificate['weights']
        scale = certificate['scale']
        assert type(scale) is int and scale > 0
        assert len(weights) == len(model['rows'])
        weighted_columns = [0] * 574
        weighted_rhs = 0
        for row, weight in zip(model['rows'], weights):
            assert type(weight) is int and row['sense'] in ('eq', 'le')
            assert row['sense'] == 'eq' or weight >= 0
            assert type(row['rhs']) is int
            weighted_rhs += weight * row['rhs']
            terms = row['terms']
            assert terms == sorted(terms) and len({i for i, a in terms}) == len(terms)
            for i, a in terms:
                assert type(i) is int and 0 <= i < 574 and type(a) is int and a != 0
                weighted_columns[i] += weight * a
        residual = [scale * c - a for c, a in zip(model['objective'], weighted_columns)]
        positive = [max(0, a) for a in residual]
        numerator = weighted_rhs + sum(positive)
        bound = Fraction(numerator, scale)
        assert certificate['residual'] == residual
        assert certificate['positive_residual'] == positive
        assert certificate['upper_numerator'] == numerator
        assert rational(certificate['upper_bound']) == rational(native['exact_upper']) == bound
        assert bound == Fraction(95955197 if root == 0 else 95763979, 1000000)
        assert bound < 96
        reports.append({
            'root': root, 'preserved_square_rows': old_rows, 'total_rows': len(model['rows']),
            'variables': 574, 'added_cycle_parity_rows': len(parity_records),
            'cycle_length_counts': dict(sorted(Counter(r['cycle_length'] for r in parity_records).items())),
            'parity_rows': parity_records, 'new_subset_rows': subset_records,
            'dual_certificate': {'scale': scale, 'weighted_rhs': weighted_rhs,
                                'positive_residual_sum': sum(positive),
                                'upper_numerator': numerator, 'exact_upper': pair(bound),
                                'gap_below96': pair(96 - bound),
                                'nonzero_weights': sum(w != 0 for w in weights),
                                'residual_coordinates_checked': len(residual)},
            'prefix_consequence': {'excluded_odd_edge_partner_length': 95,
                                   'maximum_arbitrary_partner_edges': 94,
                                   'fixed_parent_one_crossing_join_edges': 193},
            'pins': pins([model_path, folder / 'native-result.json', folder / 'upper-certificate.json', base_path]),
        })
    report = {
        'status': 'PASS_EXACT_LONG_CYCLE_ROWS_AND_UPPER_CERTIFICATES',
        'scope': 'Independent integer reconstruction of every added row, preserved square-model prefixes, and exact dual-residual bounds. No optimizer, compiler, software tests, or numerical optimality assumption.',
        'models': reports, 'execution': execution,
        'primal_scope': 'Excluded from this frozen baseline; later terminal primal, flow, and potential evidence requires a separate extension.',
        'logical_scope': 'At roots 0 and 78 of the saved 98-edge parent only. Any longer admissible partner has an excluded 95-edge prefix. The 193 bound concerns one-crossing joins with this parent; no global bound or witness is established.',
        'lean_scope': 'Generic CutParity221 is separate. This numerical array audit is not an end-to-end Lean assembly.',
        'pins': pins([Path(__file__), prior_path, HOME / 'scripts/long_separation.py',
                      HOME / 'scripts/run_long.py', HOME / 'data/long-execution.json',
                      HOME / 'data/long-summary.json']),
    }
    (HOME / 'data/long-audit.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': report['status'], 'models': [
        {k: item[k] for k in ('root', 'total_rows', 'added_cycle_parity_rows', 'cycle_length_counts', 'dual_certificate')}
        for item in reports]}, indent=2))


if __name__ == '__main__':
    main()
