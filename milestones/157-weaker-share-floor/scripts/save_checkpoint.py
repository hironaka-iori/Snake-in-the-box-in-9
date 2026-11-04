"""Verify the prepared test and accepted arithmetic without executing research jobs."""
from pathlib import Path
import hashlib
import json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))

def main():
    prep = read(H/'data/preparation.json')
    assert prep['status'] == 'SOURCE_PREPARED_NOT_EXECUTED'
    assert digest(R/prep['plan_path']) == prep['plan_sha256']
    for mapping in [prep['script_pins'], prep['input_pins'], prep['accepted156_pins']]:
        for path, expected in mapping.items():
            assert digest(R/path) == expected, path
    lean = read(H/'data/affine-lean-check.json')
    assert lean['status'] == 'PASS' and lean['exit_code'] == 0 and len(lean['axioms']) == 5
    for theorem in lean['axioms']:
        assert set(theorem['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    for path, expected in lean['dependencies'].items():
        assert digest(path) == expected, path
    assert digest(lean['log']) == lean['log_sha256']
    assert digest(lean['object']) == lean['olean_sha256']
    attempt = read(H/'data/launch-attempt.log')
    assert attempt['status'] == 'NOT_STARTED_RESOURCE_GATE'
    assert attempt['reason'] == 'LOW_FREE_MEMORY'
    assert attempt['resources']['free_bytes'] < 3*1024**3
    assert not (R/'work/fullgraph-active.lock').exists()
    assert not (H/'data/floor17-range496').exists()
    for path in [R/'paper/snake9_research.tex', Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')]:
        assert digest(path) == 'e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb'
    evidence = ['data/preparation.json', 'data/experiment-plan.json', 'data/affine-lean-check.json',
                'data/affine-receipt-recovery.json', 'data/launch-attempt.log',
                'MATHEMATICAL_NOTE.md', 'CHECKPOINT.md', 'scripts/save_checkpoint.py']
    receipt = dict(status='PASS_ARITHMETIC_AND_PREPARATION_GRAPH_TEST_PENDING',
        evidence_sha256={p:digest(H/p) for p in evidence},
        Lean_arithmetic_statements=5, graph_test_executed=False,
        experiment_status='NOT_STARTED_RESOURCE_GATE',
        hypothesis='012034floor17 admits mean496 and integer range603 through631 on the retained conditional graph.',
        hypothesis_resolved=False, new_global_bound=False,
        startup_available_bytes=attempt['resources']['free_bytes'], startup_required_bytes=3*1024**3,
        pending_command='python -B -X utf8 milestones/157-weaker-share-floor/scripts/run_potential.py --label floor17-range496',
        paper_last_full_revision=156, paper_next_full_revision=166)
    (H/'data/checkpoint.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(receipt['status'])

if __name__ == '__main__':
    main()
