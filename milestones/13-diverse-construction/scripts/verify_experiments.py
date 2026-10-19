"""Independent saved-witness and experiment-consistency checks, not UNSAT proofs."""
import hashlib
import itertools
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'milestones/12-construction-196/scripts'))
from audit_results import check


def sha(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def canonical(path):
    def key(vertices):
        labels = {}
        result = []
        for a, b in zip(vertices, vertices[1:]):
            d = a^b
            if d not in labels:
                labels[d] = len(labels)
            result.append(labels[d])
        return tuple(result)
    return min(key(path), key(path[::-1]))


def main():
    bank = json.loads((ROOT/'work/bank9.json').read_text(encoding='utf-8'))
    bank_keys = {canonical(row['vertex_sequence']): i for i,row in enumerate(bank)}
    out = {'status': 'PASSED', 'scope': 'Pair counts, symmetry keys, and recorded repair bookkeeping; no UNSAT certification.',
           'hash_normalization': 'CRLF to LF', 'searches': {}, 'repairs': {}, 'sha256': {}}
    for p in sorted((HERE/'data').glob('*.json')):
        if p.name == 'verification.json':
            continue
        d = json.loads(p.read_text(encoding='utf-8'))
        out['sha256'][p.relative_to(ROOT).as_posix()] = sha(p)
        if 'capacity' in d:
            assert len(d['best_walk']) == d['target_edges']+1
            dup, chords = check(d['best_walk'])
            assert (len(dup),len(chords)) == (d['duplicate_pairs'],d['chord_pairs'])
            assert d['best_energy'] == 4*len(dup)+len(chords)
            assert check(d['best_valid_segment']) == ([], [])
            assert len(d['best_valid_segment']) == d['best_valid_edges']+1
            assert d['pool_size'] == len(d['pool']) <= d['capacity']
            assert d['best_score_classes_seen'] >= d['pool_size']
            keys = set()
            for walk in d['pool']:
                assert len(walk) == d['target_edges']+1
                a,b = check(walk)
                assert 4*len(a)+len(b) == d['best_energy']
                keys.add(canonical(walk))
            assert len(keys) == len(d['pool'])
            assert d['proposals'] == d['proposal_budget'] or d['best_energy'] == 0
            out['searches'][p.name] = {k:d[k] for k in ('seed','capacity','proposals','best_energy',
                'duplicate_pairs','chord_pairs','best_valid_edges','best_score_classes_seen','pool_size','seconds','delta_audits')}
            out['searches'][p.name]['chord_indices'] = chords
            out['searches'][p.name]['prefix191_bank_representative'] = bank_keys.get(canonical(d['best_walk'][:192]))
        elif 'rounds' in d:
            source = ROOT/d['source']
            assert sha(source) == d['source_sha256']
            seed = json.loads(source.read_text(encoding='utf-8'))
            walk = seed['best_valid_segment'] if d['control'] else (
                seed['best_walk'] if d['member'] < 0 else seed['pool'][d['member']])
            dup,chords = check(walk)
            assert not dup and chords == d['chord_pairs']
            cover = set(d['initial_cover_positions'])
            assert all(a in cover or b in cover for a,b in chords)
            # Independent minimum-cardinality check over endpoints of the small chord graph.
            ends = sorted({i for e in chords for i in e})
            for size in range(len(cover)):
                assert not any(all(a in c or b in c for a,b in chords)
                    for c in map(set,itertools.combinations(ends,size)))
            fixed = {v for i,v in enumerate(walk) if i not in cover}
            for row in d['rounds']:
                assert sorted(fixed) == row['fixed_vertices']
                if 'core_vertices' in row:
                    assert row['status'] == 'INFEASIBLE'
                    assert set(row['core_vertices']) <= fixed
                if 'released_vertices' in row:
                    drop = set(row['released_vertices'])
                    assert drop <= fixed and drop & set(row['core_vertices'])
                    fixed -= drop
            assert sorted(fixed) == d['remaining_fixed_vertices']
            if 'witness' in d:
                assert check(d['witness']) == ([], [])
                assert len(d['witness']) == d['target_edges']+1 and fixed <= set(d['witness'])
            out['repairs'][p.name] = {'status': d['status'], 'cover_size': len(cover),
                'rounds': len(d['rounds']), 'final_fixed': len(fixed), 'seconds': d['total_seconds'],
                'infeasible_rounds': sum(r['status']=='INFEASIBLE' for r in d['rounds']),
                'core_sizes': [len(r['core_vertices']) for r in d['rounds'] if 'core_vertices' in r]}
    for p in sorted((HERE/'scripts').glob('*')):
        if p.is_file():
            out['sha256'][p.relative_to(ROOT).as_posix()] = sha(p)
    for relative in ('work/neighborhood_search.py','work/exact_search.py','work/check_snake.py','work/bank9.json',
                     'milestones/12-construction-196/scripts/audit_results.py',
                     'milestones/12-construction-196/scripts/repair_walk.py',
                     'milestones/12-construction-196/lean/DefectCriterion.lean'):
        out['sha256'][relative] = sha(ROOT/relative)
    (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':out['status'],'repairs':out['repairs']},indent=2))


if __name__ == '__main__':
    main()
