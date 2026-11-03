"""Read-only witness/cycle audit; --output creates new evidence without overwriting."""
from pathlib import Path
from fractions import Fraction
from itertools import combinations
import argparse, gzip, hashlib, json, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'work/solver_packages'))
import numpy as np

pins = {}
def pin(path):
    path = Path(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    pins[path.relative_to(ROOT).as_posix()] = digest
    return digest

def read(path):
    pin(path)
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))

def canon(word):
    labels = {}
    return [labels.setdefault(int(x), len(labels)) for x in word]

def shape(word):
    return min(canon(word), canon(word[::-1]))

pin(ROOT / 'milestones/10-window-aggregate/scripts/gen_lean_sat.py')
witnesses = []
for name in ['012034-middle445', '012034-upper55455', '012034-middle545-pair9']:
    data = read(HERE / 'data/probes' / (name + '.json'))
    assert data['status'] == 'SAT_LOCAL_WITNESS'
    window = [0]
    for d in data['directions']:
        window.append(window[-1] ^ (1 << d))
    selected = set(data['selected'])
    ball = {v for v in range(512) if any((v ^ c).bit_count() <= 4 for c in window[1:-1])}
    assert len(selected) == len(data['selected']) and selected <= ball and set(window) <= selected
    adj = {v: {v ^ (1 << d) for d in range(9)} & selected for v in selected}
    assert all(len(ns) <= 2 for ns in adj.values())
    interior = {v for v in selected if all(v ^ (1 << d) in ball for d in range(9))}
    assert all(len(adj[v]) >= 1 for v in interior)
    endpoints = sorted(v for v in interior if len(adj[v]) == 1)
    assert len(endpoints) <= 2
    unseen = set(selected)
    components = []
    while unseen:
        component = {unseen.pop()}
        todo = list(component)
        while todo:
            v = todo.pop()
            fresh = adj[v] & unseen
            unseen -= fresh
            component |= fresh
            todo.extend(fresh)
        assert sum(len(adj[v]) for v in component) == 2 * (len(component) - 1)
        components.append(len(component))
    # Check the encoder's explicit square and six-cycle constraints directly.
    cut_count = 0
    for v in ball:
        for a, b in combinations(range(9), 2):
            if (v >> a) & 1 or (v >> b) & 1:
                continue
            sq = {v, v | (1 << a), v | (1 << b), v | (1 << a) | (1 << b)}
            if sq <= ball:
                assert not sq <= selected
                cut_count += 1
        for dims in combinations(range(9), 3):
            if any((v >> k) & 1 for k in dims):
                continue
            cube = [v ^ sum(1 << dims[j] for j in range(3) if (r >> j) & 1) for r in range(8)]
            if set(cube) <= ball:
                for r in range(4):
                    assert not {cube[j] for j in range(8) if j not in (r, 7-r)} <= selected
                    cut_count += 1
    for cut in data['cycle_cuts']:
        cs = set(cut)
        assert len(cs) == len(cut) and not cs <= selected
        assert all(sum(v ^ (1 << d) in cs for d in range(9)) == 2 for v in cs)
    alpha = []
    for i, c in enumerate(window[1:-1], 1):
        used = {c ^ window[i-1], c ^ window[i+1]}
        corners = [c ^ (1 << a) ^ (1 << b) for a, b in combinations(range(9), 2)
                   if (1 << a) not in used and (1 << b) not in used]
        assert len(corners) == 21
        alpha.append(sum(v not in selected for v in corners))
    assert alpha == data['census']['alpha']
    assert all(lo <= x <= hi for x, (lo, hi) in zip(alpha, data['bounds']))
    total = sum(alpha[j] for j in data['positions'])
    assert total <= data['cap']
    witnesses.append(dict(name=name, window=window, selected_vertices=len(selected),
        ball_vertices=len(ball), alpha=alpha, tested_sum=total, cap=data['cap'],
        components=sorted(components, reverse=True), interior_endpoints=endpoints,
        explicit_small_cycle_clauses_checked=cut_count, saved_cycle_cuts=len(data['cycle_cuts'])))

ds = read(ROOT / 'milestones/59-extended-share-window/extended/data/model.json')['extensions']
graph_path = ROOT / 'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
pin(graph_path)
with np.load(graph_path) as z:
    graph = {k: z[k] for k in z.files}
completed = read(ROOT / 'milestones/73-countfree-share-catalogue/data/proved-model.json')
cf = {tuple(x['shape']): x['share'] for x in completed['countfree_floors']}
ff = cf | {(0,1,2,0,3,2):16, (0,1,2,0,3,4):18, (0,1,2,3,0,1):16,
           (0,1,2,3,4,0):16, (0,1,2,3,4,5):16}
eight = read(HERE / 'data/pair-rules.json')
assert len(eight) == 8
for rule in eight:
    assert rule['bounds'] == rule['bounds'][::-1]
    assert rule['positions'] == sorted(4-j for j in rule['positions'])

experiments = []
for label, script in [('pair24', 'evaluate_pair.py'), ('interval45454', 'evaluate_intervals.py')]:
    folder = HERE / 'data' / label
    data = read(folder / 'results.json')
    assert pin(HERE / 'scripts' / script) == data['script_sha256']
    for path, digest in data['source_files_sha256'].items():
        assert pin(ROOT / path) == digest
    removed = set(read(folder / 'removed-indices.json'))
    assert len(graph['U']) - len(removed) == data['edges']
    profiles = []
    for profile in data['profiles']:
        cycle = profile['cycle']
        floors = cf if profile['profile'] == 'completed' else ff
        potential_path = folder / profile['potential_file']
        pin(potential_path)
        raw = gzip.decompress(potential_path.read_bytes())
        assert hashlib.sha256(raw).hexdigest() == profile['potential_sha256']
        pi = np.frombuffer(raw, dtype='<i8')
        assert len(pi) == data['states'] and pi.min() == 0 and pi.max() == profile['range_scaled']
        decoded = []
        for i, edge in enumerate(cycle):
            k = edge['edge']
            assert k not in removed and edge['v'] == cycle[(i+1) % len(cycle)]['u']
            for key, array in [('u','U'), ('v','V'), ('direction','direction'),
                               ('history','history'), ('count_code','count_code')]:
                assert edge[key] == int(graph[array][k])
            digits = [edge['count_code'] // 6**j % 6 + 1 for j in range(5,-1,-1)]
            placements = []
            for s in [0,1]:
                word = ds[edge['direction']][s+2:s+8]
                values = digits[s:s+5]
                reverse = canon(word[::-1]) < canon(word)
                rule_results = []
                for rule in eight:
                    applicable = shape(word) == shape(rule['directions']) and all(
                        lo <= v and (21 if v == 6 else v) <= hi
                        for v,(lo,hi) in zip(values,rule['bounds']))
                    deficit = max(0, rule['lower'] - sum(values[j] for j in rule['positions'])) if applicable else 0
                    if label == 'pair24':
                        assert not (deficit and all(values[j] < 6 for j in rule['positions']))
                        if s == 1:
                            assert deficit == 0
                    rule_results.append(dict(name=rule['name'],applicable=applicable,deficit=deficit))
                if s == 1 and label == 'interval45454':
                    assert all(x['deficit'] == 0 for x in rule_results[:7])
                placements.append(dict(offset=s,raw_directions=word,reverse=reverse,
                    canonical_shape=shape(word),counts=values[::-1] if reverse else values,
                    rules=rule_results))
            base = max(int(graph['weight'][k]),120*digits[-1]+floors.get(tuple(shape(ds[edge['direction']][-6:])),0))
            assert edge['bonus'] == 0 and edge['weight'] == base
            assert profile['p']+int(pi[edge['v']]) <= profile['d']*base+int(pi[edge['u']])
            decoded.append(dict(edge=k,di=edge['direction'],q=edge['history'],code=edge['count_code'],
                counts6=digits,weight=base,placements=placements))
        mean = Fraction(sum(e['weight'] for e in cycle),len(cycle))
        comparison = Fraction(1098960*profile['d']+8*profile['p']+profile['range_scaled'],4200*profile['d']+profile['p'])
        assert mean == Fraction(profile['mean']) == Fraction(profile['p'],profile['d'])
        assert comparison == Fraction(profile['comparison_bound'])
        assert comparison.numerator//comparison.denominator == profile['comparison_integer_bound']
        profiles.append(dict(profile=profile['profile'],mean=str(mean),range_scaled=profile['range_scaled'],
            comparison=str(comparison),integer_comparison=profile['comparison_integer_bound'],cycle=decoded))
    experiments.append(dict(label=label,edges=data['edges'],additional_to_previous_family=data['additional_to_previous_family'],profiles=profiles))

receipt = read(HERE / 'data/PairGeometry113-audit.json')
assert receipt['status'] == 'PASS_PAIR_GEOMETRY' and receipt['exit_code'] == 0 and not receipt['timeout']
assert pin(HERE / 'lean/PairGeometry113.lean') == receipt['source_sha256']
assert pin(HERE / 'build-pair-geometry/PairGeometry113.olean') == receipt['olean_sha256']
assert pin(HERE / receipt['log']) == receipt['log_sha256']
assert pin(HERE / receipt['source_snapshot']) == receipt['source_sha256']
source = (HERE / 'lean/PairGeometry113.lean').read_text(encoding='utf-8')
assert '(hlocal : ∀ S E : Nat → Bool,' in source and 'apply hlocal _ _ ax' in source
assert all(set(t['axioms']) <= {'propext','Classical.choice','Quot.sound'} for t in receipt['theorem_audits'])
timeouts = []
for name in ['012034-middle545-pair8','012034-middle545-pair8-plain']:
    data = read(HERE / 'data' / (name+'-solver.json'))
    assert data['status'] == 'TIMEOUT' and data['timeout_seconds'] == 30
    assert pin(Path(data['command'][-2])) == data['cnf_sha256']
    assert pin(Path(data['command'][-1])) == data['raw_sha256']
    assert Path(data['command'][-1]).stat().st_size == data['raw_bytes']
    timeouts.append(dict(name=name,status=data['status'],seconds=data['seconds'],raw_bytes=data['raw_bytes']))

out = dict(status='PASS_BOUNDED_INDEPENDENT_REVIEW',witnesses=witnesses,experiments=experiments,
    pair_geometry_conditional=True,pair_geometry_axioms=receipt['theorem_audits'],
    native_proof_attempts=timeouts,source_pins=pins,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    scope='Direct local-model checks and saved-cycle/full-key checks only. No solver, Lean compiler or full-edge graph scan. The pair inequality still needs its local contradiction; no new global bound.')
parser = argparse.ArgumentParser()
parser.add_argument('--output',type=Path)
args = parser.parse_args()
text = json.dumps(out,indent=2)+'\n'
if args.output:
    with args.output.open('x',encoding='utf-8') as f:
        f.write(text)
    print(json.dumps(dict(status=out['status'],witnesses=len(witnesses),experiments=len(experiments),
        output=str(args.output),sha256=hashlib.sha256(args.output.read_bytes()).hexdigest()),indent=2))
else:
    print(text,end='')
