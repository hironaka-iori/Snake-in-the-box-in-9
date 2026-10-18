"""Independently recount all saved pairs; emit a reproducible pilot summary."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]


def check(path):
    assert path and all(type(v) is int and 0 <= v < 512 for v in path)
    assert all((a ^ b).bit_count() == 1 for a, b in zip(path, path[1:]))
    duplicates, chords = [], []
    for j, b in enumerate(path):
        for i, a in enumerate(path[:j]):
            if a == b:
                duplicates.append([i, j])
            elif j > i+1 and (a ^ b).bit_count() == 1:
                chords.append([i, j])
    return duplicates, chords


def sha(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def main():
    summary = {'status': 'PASSED', 'scope': 'Saved outputs and source identity only; no search completeness claim.',
               'hash_normalization': 'CRLF to LF', 'walks': {}, 'repairs': {}, 'sha256': {}}
    for path in sorted(HERE.glob('data/*.json')):
        if path.name == 'pilot-summary.json':
            continue
        data = json.loads(path.read_text(encoding='utf-8'))
        summary['sha256'][path.relative_to(ROOT).as_posix()] = sha(path)
        if 'best_walk' in data:
            duplicates, chords = check(data['best_walk'])
            assert len(data['best_walk']) == data['target_edges']+1
            assert len(duplicates) == data['duplicate_pairs']
            assert len(chords) == data['chord_pairs']
            assert data['best_energy'] == 4*len(duplicates)+len(chords)
            assert check(data['best_valid_segment']) == ([], [])
            assert len(data['best_valid_segment']) == data['best_valid_edges']+1
            assert (data['best_energy'] > 0) == (data['status'] == 'NO_WITNESS')
            summary['walks'][path.name] = {k: data[k] for k in
                ('target_edges', 'seed', 'seed_index', 'seconds', 'proposals', 'delta_audits',
                 'initial_energy', 'best_energy', 'duplicate_pairs', 'chord_pairs', 'best_valid_edges')}
            summary['walks'][path.name]['chord_indices'] = chords
        elif 'fixed_vertices' in data:
            source = ROOT/data['source']
            assert data['source_hash_normalization'] == 'CRLF to LF'
            assert sha(source) == data['source_sha256']
            seed = json.loads(source.read_text(encoding='utf-8'))
            walk = seed['best_valid_segment'] if data['control_fixed_valid_path'] else seed['best_walk']
            duplicates, chords = check(walk)
            assert duplicates == data['input_duplicate_pairs'] and chords == data['input_chord_pairs']
            conflicts = {i for pair in duplicates+chords for i in pair}
            released = {i for i in range(len(walk)) if i < 10 or i >= len(walk)-10 or
                        any(abs(i-j) <= data['radius_along_walk'] for j in conflicts)}
            fixed = set(walk) if data['control_fixed_valid_path'] else {
                v for i, v in enumerate(walk) if i not in released}
            assert sorted(fixed) == data['fixed_vertices']
            assert data['released_positions'] == ([] if data['control_fixed_valid_path'] else sorted(released))
            if 'witness' in data:
                assert check(data['witness']) == ([], [])
                assert len(data['witness']) == data['target_edges']+1
                assert fixed <= set(data['witness'])
            summary['repairs'][path.name] = {k: data[k] for k in
                ('target_edges', 'radius_along_walk', 'status', 'seconds', 'branches', 'conflicts')}
            summary['repairs'][path.name]['fixed_vertices'] = len(fixed)
            summary['repairs'][path.name]['released_positions'] = len(data['released_positions'])
    for folder in ('scripts', 'lean', 'logs'):
        for path in sorted((HERE/folder).glob('*')):
            if path.is_file():
                summary['sha256'][path.relative_to(ROOT).as_posix()] = sha(path)
    for relative in ('work/neighborhood_search.py', 'work/exact_search.py', 'work/check_snake.py', 'work/bank9.json'):
        summary['sha256'][relative] = sha(ROOT/relative)
    receipt = json.loads((ROOT/'outputs/lean112/bank-proof.json').read_text(encoding='utf-8'))
    assert receipt['status'] == 'PASSED' and len(receipt['entries']) == 262
    assert all(row['status'] == 'PASSED' for row in receipt['entries'].values())
    summary['collaborator_keep112_receipt'] = {'entries': 262, 'status': receipt['status'],
                                              'sha256': sha(ROOT/'outputs/lean112/bank-proof.json')}
    (HERE/'data/pilot-summary.json').write_text(json.dumps(summary, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: summary[k] for k in ('status', 'repairs')}, indent=2))


if __name__ == '__main__':
    main()
