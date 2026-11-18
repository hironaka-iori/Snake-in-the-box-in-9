"""Reconstruct archived mathematical inputs without a solver or compiler.

Only a new audit receipt is written. The full screening enumeration is not
rerun, and recorded native infeasibility is not promoted to a kernel proof.
"""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import argparse
import ast
import hashlib
import importlib.util
import json
import re
import time
from zipfile import ZipFile


H = Path(__file__).resolve().parents[1]
R = H.parents[1]
BASES = R / 'milestones/236-parity-exchange-frontier/data/bases.json'
PINS = {}


def sha(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()


def pin(path, expected=None):
    path = Path(path).resolve()
    digest = sha(path)
    assert expected is None or digest == expected, str(path)
    key = str(path)
    assert key not in PINS or PINS[key] == digest, key
    PINS[key] = digest
    return digest


def read(path):
    pin(path)
    return json.loads(Path(path).read_bytes())


def main():
    if not __debug__:
        raise RuntimeError('This mathematical audit requires assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-name', default='finite-input-audit.json')
    args = parser.parse_args()
    assert re.fullmatch(r'[A-Za-z0-9_-]+\.json', args.receipt_name)
    destination = H / 'data' / args.receipt_name
    assert not destination.exists(), 'Preserve the existing receipt; choose another receipt name.'
    start = time.monotonic()
    pin(Path(__file__))

    raw_bases = read(BASES)
    for path, digest in raw_bases['pins'].items():
        pin(path, digest)
    bases = raw_bases['bases']
    assert [base['id'] for base in bases] == list(range(145))
    for base in bases:
        vertices = base['vertices']
        assert vertices == sorted(set(vertices)) and len(vertices) == 96
        assert all(isinstance(v, int) and 0 <= v < 512 for v in vertices)
        assert len({v.bit_count() % 2 for v in vertices}) == 1

    # Import the previously reviewed inspection function, never its main.
    inspection_path = H / 'degree/audit_majority.py'
    pin(inspection_path)
    spec = importlib.util.spec_from_file_location('archived_majority_inspection', inspection_path)
    inspection = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(inspection)
    assert inspection.BASES.resolve() == BASES.resolve()
    result = read(H / 'degree/majority-one.json')
    assert result['base_sha256'] == pin(BASES)
    pin(H / 'degree/majority_survey.py', result['script_sha256'])
    assert result['arguments']['bases'] is None
    assert [record['base'] for record in result['results']] == list(range(145))
    old_audit = read(H / 'degree/audit.json')
    archive_path = H / 'degree/majority-one-models.zip'
    pin(archive_path, old_audit['archives']['majority-one'])
    degree_count = 0
    with ZipFile(archive_path) as archive:
        assert len(archive.namelist()) == len(set(archive.namelist())) == 145
        seen_models = set()
        for record in result['results']:
            assert record['status'] == 'INFEASIBLE' and len(record['iterations']) == 1
            item = record['iterations'][0]
            assert item['status'] == 'INFEASIBLE' and not item.get('cycles', [])
            expected_name = f"base{record['base']:03d}-iteration0.pbtxt"
            assert item['model'] == expected_name
            content = archive.read(expected_name)
            assert hashlib.sha256(content).hexdigest() == item['sha256']
            inspection.inspect(content, bases[record['base']]['vertices'], [])
            seen_models.add(expected_name)
            degree_count += 1
        assert seen_models == set(archive.namelist())
    assert old_audit['models'] == old_audit['classes'] == degree_count == 145
    assert old_audit['outcomes'] == {'INFEASIBLE': 145}

    decisions = read(H / 'majority/decisions.json')
    cuts = read(H / 'majority/cuts.json')
    assert len(decisions) == len(cuts) == 623
    for path in ['majority/CubeCut.lean', 'majority/make_cut_proofs.py',
                 'majority/cuts.py', 'majority/finish.py', 'majority/screen.cpp']:
        pin(H / path)
    vertex_sets = []
    seen_sets = set()
    seen_descriptions = set()
    cut_gaps = Counter()
    for group, cut in zip(decisions, cuts):
        descriptions = group['descriptions']
        assert descriptions
        reconstructed = []
        for identifier, removed, added_a, added_b in descriptions:
            description = (identifier, removed, added_a, added_b)
            assert description not in seen_descriptions
            seen_descriptions.add(description)
            assert 0 <= identifier < 145
            old = set(bases[identifier]['vertices'])
            assert removed in old and added_a not in old and added_b not in old
            assert 0 <= added_a < added_b < 512
            vertices = (old - {removed}) | {added_a, added_b}
            assert len(vertices) == 97 and len({v.bit_count() % 2 for v in vertices}) == 1
            reconstructed.append(frozenset(vertices))
        assert len(set(reconstructed)) == 1
        vertices = set(reconstructed[0])
        assert reconstructed[0] not in seen_sets
        seen_sets.add(reconstructed[0])
        vertex_sets.append(vertices)

        source, target = cut['s'], cut['t']
        assert len(source) == len(set(source)) and len(target) == len(set(target))
        assert 512 not in source and 512 in target
        proper_target = set(target) - {512}
        assert set(source) <= vertices and proper_target <= vertices
        graph = {v: set() for v in vertices}
        for label in range(512):
            partners = vertices.intersection(label ^ (1 << j) for j in range(9))
            if len(partners) == 2:
                u, v = partners
                graph[u].add(v)
                graph[v].add(u)
        escaping = sum(len(graph[u] - proper_target) for u in source)
        assert escaping == cut['escaping']
        excess = 2 * len(source) - 2 * len(proper_target) - 2 - escaping
        assert excess > 0
        cut_gaps[excess] += 1
    assert len(seen_descriptions) == 679 and len(seen_sets) == 623
    assert dict(cut_gaps) == {2: 161, 4: 291, 6: 167, 8: 4}

    declaration_pattern = (r'theorem cut237_(\d+) : violated (\d+)\s+'
                           r'(\[[^\]]*\]) (\[[^\]]*\]) = true := by decide \+kernel')
    mapped = {}
    module_count = 0
    for path in sorted((H / 'majority/certificates').glob('Cuts*.lean')):
        pin(path)
        text = path.read_text(encoding='utf-8')
        declarations = re.findall(declaration_pattern, text)
        assert len(declarations) == text.count('theorem cut237_')
        assert declarations
        module_count += 1
        for index, mask, source, target in declarations:
            k = int(index)
            assert 0 <= k < 623 and k not in mapped
            mapped[k] = path.name
            assert int(mask) == sum(1 << v for v in vertex_sets[k])
            assert ast.literal_eval(source) == cuts[k]['s']
            assert ast.literal_eval(target) == [v for v in cuts[k]['t'] if v != 512]
    assert set(mapped) == set(range(623)) and module_count == 25

    independent = read(H / 'degree/independent-results.json')
    for field, path in [('source', H / 'degree/independent_screen.cpp'),
                        ('check_script', H / 'degree/independent_check.py'),
                        ('bases', BASES), ('archive', H / 'majority/decisions.json')]:
        pin(path, independent[field])
    assert independent['circuit_outcomes'] == {'INFEASIBLE': 623}
    assert len(independent['per_group']) == 623
    assert set(independent['per_group']) == {'INFEASIBLE'}
    assert independent['exact_input_descriptions'] == 145 * 96 * 160 * 159 // 2 == 177062400
    assert independent['surviving_descriptions'] == 679 and independent['distinct_graphs'] == 623
    assert [row[0] for row in independent['per_base']] == list(range(145))
    assert sum(row[1] for row in independent['per_base']) == independent['final_graphs_evaluated'] == 430488
    assert sum(row[2] for row in independent['per_base']) == 679
    assert all(sha(path) == digest for path, digest in PINS.items())

    receipt = dict(
        status='PASS_FINITE_INPUT_AUDIT', finished_utc=datetime.now(timezone.utc).isoformat(),
        degree_models_reconstructed=degree_count, degree_classes=145,
        recorded_degree_outcomes={'INFEASIBLE': 145}, degree_cycle_cuts=0,
        descriptions_reconstructed=679, distinct_sets_reconstructed=623,
        contraction_graphs_reconstructed=623, cut_inequalities_recomputed=623,
        cut_gap_distribution=dict(sorted(cut_gaps.items())),
        certificate_declarations_mapped=623, certificate_modules=module_count,
        recorded_circuit_outcomes={'INFEASIBLE': 623},
        recorded_full_enumeration_descriptions=177062400,
        full_enumeration_rerun=False, solver_rerun=False, compiler_run=False,
        source_and_input_pins=PINS, seconds=time.monotonic() - start,
        scope='Exact read-only reconstruction of archived degree models, surviving edited sets, contraction edges, cut counts and original Lean declaration inputs.',
        limitations=[
            'Native INFEASIBLE is a recorded solver result, not a contradiction replay.',
            'The full 177062400-description enumeration was not rerun.',
            'Original Lean declarations were mapped to inputs, not compiled in this audit.',
            'The independent executable binary digest was not revalidated against a located executable.',
            'The graph-to-path interpretation and current kernel acceptance are separate obligations.'])
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps({k: receipt[k] for k in [
        'status', 'degree_models_reconstructed', 'descriptions_reconstructed',
        'distinct_sets_reconstructed', 'cut_inequalities_recomputed',
        'certificate_declarations_mapped', 'certificate_modules', 'seconds']}, indent=2))


if __name__ == '__main__':
    main()
