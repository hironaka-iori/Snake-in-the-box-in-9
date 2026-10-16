"""Audit bank identity, inducedness and coverage of generated regrowth sources.

This executable data audit supplements, and does not replace, Lean compilation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tag')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not re.fullmatch(r'\d+(?:v2)?', args.tag):
        ap.error('Expected a certificate tag such as 144v2')
    project = ROOT / 'work/final_lean'
    bank_file = ROOT / 'work/bank9.json'
    bank = [row['vertex_sequence'] for row in json.loads(bank_file.read_text())]
    for number, path in enumerate(bank):
        assert len(path) == 192 and len(set(path)) == 192, number
        assert all(0 <= v < 512 for v in path), number
        for i, v in enumerate(path):
            for j in range(i + 1, len(path)):
                assert ((v ^ path[j]).bit_count() == 1) == (j == i + 1), (number, i, j)
    oriented = [path for s in bank for path in (s, s[::-1])]
    data_source = (project/'DfsBankData.lean').read_text()
    arrays = re.findall(r'^def o(\d+) : Array Nat := #\[([^\]]*)\]', data_source, re.M)
    assert len(arrays) == len(oriented)
    for (index, values), expected_index, path in zip(arrays, range(len(oriented)), oriented):
        assert int(index) == expected_index
        assert [int(v.strip()) for v in values.split(',')] == path, expected_index
    listed = re.search(r'def orientedList : List \(Array Nat\) := \[([^\]]*)\]', data_source)
    assert listed and re.findall(r'o\d+', listed[1]) == [f'o{i}' for i in range(len(oriented))]
    assert 'def oriented (j : Nat) : Array Nat := orientedList[j]!' in data_source
    aggregate = f'DfsBankCert{args.tag}'
    modules = {f.stem: f for f in project.glob(aggregate+'_*.lean')}
    visited, pending = set(), [aggregate]
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        path = project/(name+'.lean')
        assert path.is_file(), name
        for imported in re.findall(r'^import (\w+)$', path.read_text(), re.M):
            if imported.startswith(aggregate):
                pending.append(imported)
    assert visited - {aggregate} == set(modules), 'Orphan or missing certificate module'
    combined = '\n'.join(path.read_text() for path in modules.values())
    entries = re.findall(r'^theorem keep'+args.tag+r'_(\d+)\s*:', combined, re.M)
    assert sorted(map(int, entries)) == list(range(len(oriented))), 'Missing or duplicate entry theorem'
    summary = dict(status='PASSED', tag=args.tag,
        bank_sha256=hashlib.sha256(bank_file.read_bytes()).hexdigest(),
        bank_paths=len(bank), all_bank_paths_induced_191_edge_snakes=True,
        oriented_entries=len(oriented), all_arrays_and_order_match=True,
        reachable_dependency_modules=len(modules), entry_theorems=len(entries),
        generated_theorems=len(re.findall(r'^theorem ', combined, re.M)),
        scope='Executable bank and coverage audit. Lean compilation is required separately.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
