"""Bounded radius-four count-sum tests with preserved literal multiplicity."""
from pathlib import Path
from itertools import combinations
import argparse, hashlib, json, sys, time
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path[:0] = [str(ROOT / 'milestones/28-direct-share-certificates/scripts'), str(ROOT / 'work/solver_packages')]
from tagged_share import TaggedEncoding, Cadical153
from direct import window, census
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
ap = argparse.ArgumentParser()
ap.add_argument('--input', default='data/cases-initial.json')
ap.add_argument('--name')
ap.add_argument('--seconds', type=float, default=12)
args = ap.parse_args()
source = HERE / args.input
cases = read(source)
if args.name:
    cases = [c for c in cases if c['name'] == args.name]
assert cases
pins = {p.relative_to(ROOT).as_posix(): sha(p) for p in [source,
    ROOT / 'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
    ROOT / 'milestones/10-window-aggregate/scripts/wincert.py',
    ROOT / 'milestones/28-direct-share-certificates/scripts/tagged_share.py',
    ROOT / 'milestones/28-direct-share-certificates/scripts/direct.py']}
folder = HERE / 'data/probes'
folder.mkdir(parents=True, exist_ok=True)
for case in cases:
    path = folder / (case['name'] + '.json')
    assert not path.exists(), 'Preserve earlier attempts'
    assert len(case['bounds']) == 5 and len(case['directions']) == 6
    assert case['positions'] and all(0 <= j < 5 for j in case['positions'])
    start = time.monotonic()
    enc = TaggedEncoding(window(case['directions']), [tuple(b) for b in case['bounds']], radius=4)
    lits = []
    for j in case['positions']:
        i = j + 1
        v = enc.window[i]
        used = {v ^ enc.window[i-1], v ^ enc.window[i+1]}
        lits += [-enc.var[v ^ (1 << a) ^ (1 << b)] for a, b in combinations(range(9), 2)
            if (1 << a) not in used and (1 << b) not in used]
    assert len(lits) == 21 * len(case['positions'])
    lits.sort()
    enc.atmost(lits, case['cap'], ('unproved_sum',))
    build = time.monotonic() - start
    start = time.monotonic()
    prior_path=HERE/case['resume']
    prior=read(prior_path)
    assert prior['status']=='UNKNOWN'
    assert all(prior[k]==case[k] for k in ['directions','bounds','positions','cap'])
    pins[prior_path.relative_to(ROOT).as_posix()]=sha(prior_path)
    from gen_lean_sat import is_cycle_set
    assert all(is_cycle_set(cut) for cut in prior['cycle_cuts'])
    cuts, calls, selected, report, status = list(prior['cycle_cuts']), 0, None, None, 'UNKNOWN'
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        for cut in cuts: solver.add_clause([-enc.var[v] for v in cut])
        while time.monotonic() - start < args.seconds:
            solver.conf_budget(1000)
            result = solver.solve_limited()
            calls += 1
            if result is None:
                continue
            if not result:
                status = 'UNSAT_UNCERTIFIED'
                break
            model = solver.get_model()
            vertices = {v for v in enc.ball if model[enc.var[v]-1] > 0}
            report = census(vertices, 9, enc.window[1:-1])
            report.pop('degree')
            assert all(lo <= v <= hi for v, (lo, hi) in zip(report['alpha'], case['bounds']))
            assert sum(report['alpha'][j] for j in case['positions']) <= case['cap']
            if not report['cycles']:
                selected = sorted(vertices)
                status = 'SAT_LOCAL_WITNESS'
                break
            for cut in report['cycles']:
                assert cut and len(cut) == len(set(cut))
                assert all(sum((v ^ (1 << j)) in set(cut) for j in range(9)) >= 2 for v in cut)
                cuts.append(cut)
                solver.add_clause([-enc.var[v] for v in cut])
    assert all(sha(ROOT / p) == digest for p, digest in pins.items())
    out = dict(case, status=status, selected=selected, census=report, cycle_cuts=cuts,
        variables=enc.nv, clauses=len(enc.clauses), literal_occurrences=len(lits), distinct_literals=len(set(lits)),
        build_seconds=build, solver_seconds=time.monotonic()-start, nominal_seconds=args.seconds,
        conflict_budget_per_call=1000, calls=calls, source_files_sha256=pins, script_sha256=sha(Path(__file__)),
        scope='Native radius-four local-model evidence. All repeated literals retain their multiplicities. UNSAT lacks a checked certificate; selected local witnesses have relaxed boundaries and need independent verification. No actual-snake theorem or global bound.')
    path.write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
    print(case['name'], status, 'alpha', None if report is None else report['alpha'],
        'cuts', len(cuts), 'seconds', round(out['solver_seconds'], 3), flush=True)
