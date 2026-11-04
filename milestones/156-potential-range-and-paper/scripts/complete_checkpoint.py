"""Verify saved evidence and write a scoped completion receipt; no solver run."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def read(rel):
    return json.loads((HERE / rel).read_text(encoding='utf-8'))

def pins(mapping):
    for name, expected in mapping.items():
        p = Path(name)
        if not p.is_absolute():
            p = ROOT / p
        assert digest(p) == expected, str(p)

def main():
    result = read('data/share17-range496/result.json')
    run = read('data/share17-range496/run-status.json')
    assert result['status'] == run['status'] == 'PASS_MINIMUM_RANGE_AT_MEAN496'
    assert result['potential_range'] == result['certified_range_lower_bound'] == 602
    assert result['all_edge_inequalities_checked'] == 4661572
    assert result['minimum_slack'] == 0
    assert result['mean'] == 496 and result['occurrence_credit'] == 0
    folder = HERE / 'data/share17-range496'
    assert digest(folder / result['potential_file']) == result['potential_archive_sha256']
    for item in result['journal']:
        assert digest(folder / item['path']) == item['sha256']
    prep = read('data/preparation.json')
    pins(prep['script_pins'])
    if 'input_pins' in prep:
        pins(prep['input_pins'])
    audit = read('review/walk-audit.json')
    assert audit['status'] == 'PASS_SELECTED_ROW_WALK_AND_CYCLE_AUDIT'
    pins(audit['input_sha256'])
    lean = read('data/range-lean-check.json')
    assert lean['status'] == 'PASS' and lean['exit_code'] == 0
    assert len(lean['axioms']) == 7
    for item in lean['axioms']:
        assert set(item['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    pins(lean['dependencies'])
    assert digest(lean['log']) == lean['log_sha256']
    assert digest(lean['object']) == lean['olean_sha256']
    paper = read('data/paper-source-review.json')
    assert paper['status'] == 'PASS_FULL_PAPER_REVISION156_AND_COMPILATION'
    for path in [ROOT / 'paper/snake9_research.tex', Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')]:
        assert digest(path) == paper['paper_sha256']
    compile_record = read('data/paper-compile.json')
    assert compile_record['paper_sha256'] == paper['paper_sha256']
    assert any(json.loads(c['text']).get('kind') == 'success'
               for c in compile_record['result']['content'] if c['type'] == 'text')
    protected = {
        '.gitignore': '20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b',
        'milestones/50-three-count-return/excess-screen/data/critical-family.json': '466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82',
    }
    pins(protected)
    evidence = ['data/share17-range496/result.json', 'data/share17-range496/run-status.json',
                'data/preparation.json', 'review/walk-audit.json', 'data/range-lean-check.json',
                'data/paper-source-review.json', 'data/paper-compile.json', 'MATHEMATICAL_NOTE.md',
                'scripts/complete_checkpoint.py']
    out = {
        'status': 'PASS_SCOPED_JOINT_OPTIMUM_AND_PAPER156',
        'evidence_sha256': {p: digest(HERE / p) for p in evidence},
        'fixed_mean_range': 602, 'joint_comparison_optimum': '551765/2348',
        'equality_parameters': {'mean': 496, 'occurrence_credit': 0, 'range': 602},
        'joint_result_basis': 'Exact all-edge native certificate plus independent selected-row audit and seven Lean arithmetic theorems.',
        'native_original_scope_preserved': True, 'new_global_bound': False,
        'complete_Lean_graph_certificate': False, 'unresolved_snake_premises': True,
        'paper_sha256': paper['paper_sha256'], 'next_full_paper_revision': 166,
        'protected_files_sha256': protected,
    }
    (HERE / 'data/completion.json').write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
    print(out['status'])

if __name__ == '__main__':
    main()
