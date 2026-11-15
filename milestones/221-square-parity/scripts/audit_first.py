"""Independent exact audit of the fourteen saved first-neighbour bounds.

Only saved inputs and integer/rational arithmetic are used. No producer,
optimizer, compiler, or software-test framework is imported or invoked.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import math

ROOT = Path(__file__).resolve().parents[1]
LONG_AUDIT_HASH = 'a4c93e83583eb9abcc80f56118cbf8fa82e8de52255b2851dc7bc56f463cec54'
SUMMARY_HASH = 'fde80edbbc439321b297303ffabdab6ce330f3c017da6ef70ed0719b504ac2bb'
EXPECTED_NEIGHBOURS = {0: [2, 4, 8, 16, 32, 64, 128],
                       78: [14, 74, 76, 79, 94, 110, 206]}


def read(path):
    return json.loads(Path(path).read_bytes())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pair(value):
    return [value.numerator, value.denominator]


def main():
    prior_file = ROOT / 'data/long-audit.json'
    assert sha(prior_file) == LONG_AUDIT_HASH
    prior = read(prior_file)
    assert prior['status'] == 'PASS_EXACT_LONG_CYCLE_ROWS_AND_UPPER_CERTIFICATES'
    summary_file = ROOT / 'data/first-summary.json'
    assert sha(summary_file) == SUMMARY_HASH
    summary = read(summary_file)
    expected_cases = [(root, vertex) for root in (0, 78) for vertex in EXPECTED_NEIGHBOURS[root]]
    assert [(entry['root'], entry['first_vertex']) for entry in summary] == expected_cases
    execution_file = ROOT / 'data/first-execution.json'
    execution = read(execution_file)
    assert execution['status'] == 'ACCEPTED_NATIVE_RESULT'
    assert execution['exit_code'] == 0 and execution['stop_reason'] is None
    for name, expected in execution['pins'].items():
        assert sha(ROOT / name) == expected, name
    for stream in ('stdout', 'stderr'):
        assert sha(ROOT / f'logs/first-{stream}.log') == execution[f'{stream}_sha256']
    assert execution['summary_sha256'] == SUMMARY_HASH
    stdout = (ROOT / 'logs/first-stdout.log').read_text(encoding='utf-8').splitlines()
    assert [json.loads(line) for line in stdout if line.strip()] == summary
    assert not execution['resource_gate']['errors'] and not execution['resource_gate']['processes']
    for sample in execution['resource_samples']:
        assert not sample['errors'] and not sample['lean_processes']
    reports = []
    cover = []
    for root in (0, 78):
        model_file = ROOT / f'data/long-{root}/model.json'
        model = read(model_file)
        prior_model = next(item for item in prior['models'] if item['root'] == root)
        assert sha(model_file) == prior_model['pins'][str(model_file.relative_to(ROOT))]
        vertices = set(model['vertices'])
        neighbours = sorted(root ^ (1 << bit) for bit in range(8)
                            if root ^ (1 << bit) in vertices)
        assert neighbours == EXPECTED_NEIGHBOURS[root]
        incident = set()
        for u, v in model['edges']:
            if u == root:
                incident.add(v)
            if v == root:
                incident.add(u)
        assert sorted(incident) == neighbours
        names = model['variables']
        assert len(names) == len(set(names)) == 574
        index = {name: i for i, name in enumerate(names)}
        assert model['lower'] == [0] * 574 and model['upper'] == [1] * 574
        assert model['objective'] == [int(name.startswith('x')) for name in names]
        root_degree = [row for row in model['rows'] if row['name'] == 'root_degree']
        assert root_degree == [{'name': 'root_degree', 'terms': sorted([[index[f'x{v}'], 1] for v in neighbours]),
                                'sense': 'eq', 'rhs': 1}]
        folder = ROOT / f'data/first-{root}'
        assert {path.name for path in folder.glob('vertex-*.json')} == {
            f'vertex-{v}.json' for v in neighbours}
        cover.append({'root': root, 'allowed_first_neighbours': neighbours,
                      'literal_cube_and_edge_lists_agree': True,
                      'root_degree_is_sum_of_neighbour_selections_equal_one': True})
        for vertex in neighbours:
            path = folder / f'vertex-{vertex}.json'
            saved = read(path)
            entry = next(item for item in summary
                         if (item['root'], item['first_vertex']) == (root, vertex))
            assert sha(path) == entry['sha256']
            assert saved['root'] == root and saved['first_vertex'] == vertex
            assert saved['base_model_sha256'] == sha(model_file)
            assert saved['source_sha256'] == sha(ROOT / 'scripts/first_step.py')
            assert saved['status'] == 'OPTIMAL_NATIVE'
            branch = {'name': 'fixed_first_vertex', 'terms': [[index[f'x{vertex}'], 1]],
                      'sense': 'eq', 'rhs': 1}
            assert saved['appended_row'] == branch
            rows = model['rows'] + [branch]
            assert saved['row_count'] == len(rows)
            weights = [0] * len(rows)
            sparse = saved['nonzero_weights']
            indices = [item[0] for item in sparse]
            assert indices == sorted(set(indices))
            for item in sparse:
                assert len(item) == 2
                row_index, weight = item
                assert type(row_index) is int and 0 <= row_index < len(rows)
                assert type(weight) is int and weight != 0
                weights[row_index] = weight
            scale = saved['scale']
            assert type(scale) is int and scale > 0
            combined = [0] * len(names)
            rhs = 0
            for row, weight in zip(rows, weights):
                assert row['sense'] in ('eq', 'le')
                assert row['sense'] == 'eq' or weight >= 0
                assert type(row['rhs']) is int
                rhs += weight * row['rhs']
                for variable, coefficient in row['terms']:
                    assert type(variable) is int and 0 <= variable < len(names)
                    assert type(coefficient) is int
                    combined[variable] += weight * coefficient
            residual = [scale * objective - total
                        for objective, total in zip(model['objective'], combined)]
            assert saved['residual'] == residual and len(residual) == 574
            residual_sum = sum(value for value in residual if value > 0)
            numerator = rhs + residual_sum
            bound = Fraction(numerator, scale)
            assert saved['upper_numerator'] == numerator
            assert saved['upper_bound'] == pair(bound) == entry['upper_bound']
            assert entry['upper_float'] == float(bound)
            assert entry['objective'] == saved['objective'] and entry['seconds'] == saved['seconds']
            assert math.isfinite(saved['objective']) and math.isfinite(saved['seconds'])
            assert len(saved['values']) == 574 and all(math.isfinite(v) for v in saved['values'])
            reports.append({
                'root': root, 'first_vertex': vertex, 'row_count': len(rows),
                'nonzero_weights': len(sparse), 'zero_omitted_weights': len(rows) - len(sparse),
                'appended_row_weight': weights[-1], 'scale': scale,
                'weighted_rhs': rhs, 'positive_residual_sum': residual_sum,
                'residual_coordinates_checked': 574, 'upper_numerator': numerator,
                'exact_upper': pair(bound), 'upper_decimal': format(float(bound), '.6f'),
                'gap_below94': pair(94 - bound),
                'status_for_93_edge_partner': 'EXCLUDED' if bound < 94 else 'UNRESOLVED',
                'file': str(path.relative_to(ROOT)), 'sha256': sha(path),
            })
    exclusions = [(r['root'], r['first_vertex']) for r in reports
                  if r['status_for_93_edge_partner'] == 'EXCLUDED']
    assert exclusions == [(0, 16), (78, 14), (78, 74)]
    assert len(reports) == 14
    report = {
        'status': 'PASS_EXACT_FIRST_STEP_COVERAGE_AND_UPPER_CERTIFICATES',
        'scope': 'All fourteen saved first-step branches; independent cube-neighbour enumeration and exact sparse dual-residual arithmetic. No optimizer, compiler, software tests, or native primal feasibility claim.',
        'coverage': cover, 'branches': reports,
        'excluded_93_edge_branches': [list(case) for case in exclusions],
        'unresolved_branch_count': 11,
        'coverage_argument': 'An actual rooted induced path of length 93 has a unique first neighbour in the allowed graph. Its Boolean vertex selections satisfy exactly one listed x_first=1 branch. Root degree equals one; a later selected neighbour would create a chord. Arbitrary fractional assignments may satisfy none of the branches.',
        'limitations': 'Bounds at least 94 provide no actual partner and no exact fractional feasibility certificate. This is fixed-parent case reduction, not a global bound or complete 93-edge exclusion. Numerical objective values and rounded primal arrays are not used as proof. Generic Lean results and concrete numerical assembly remain separate.',
        'execution': {'exit_code': 0, 'stop_reason': None, 'seconds': execution['seconds'],
                      'receipt_sha256': sha(execution_file), 'summary_sha256': SUMMARY_HASH},
        'pins': {str(path.relative_to(ROOT)): sha(path) for path in (
            Path(__file__), prior_file, summary_file, execution_file,
            ROOT / 'scripts/first_step.py', ROOT / 'scripts/run_first.py',
            ROOT / 'data/long-0/model.json', ROOT / 'data/long-78/model.json')},
    }
    (ROOT / 'data/first-audit.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': report['status'], 'exclusions': exclusions,
                      'unresolved': 11, 'branches': [{key: item[key] for key in
                      ('root', 'first_vertex', 'exact_upper', 'status_for_93_edge_partner')}
                      for item in reports]}, indent=2))


if __name__ == '__main__':
    main()
