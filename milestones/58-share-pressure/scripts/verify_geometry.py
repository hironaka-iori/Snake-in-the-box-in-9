"""Independent exhaustive arithmetic checks for milestone 58 (no solver import)."""
from pathlib import Path
from fractions import Fraction
import collections, gzip, hashlib, itertools, json, sys
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'work/solver_packages'))
import numpy as np

def read(p):
    return json.loads(p.read_text())
def sha(b):
    return hashlib.sha256(b).hexdigest()
def canon(ds):
    labels = {}
    return tuple(labels.setdefault(d, len(labels)) for d in ds)
def path(ds):
    out = [0]
    for d in ds:
        out.append(out[-1] ^ (1 << d))
    return out
def encode(cs):
    out = 0
    for c in cs:
        out = 6 * out + c - 1
    return out
NB = [{x ^ (1 << d) for d in range(9)} for x in range(512)]
# Enumerate each cube face once, from its unique corner whose two varying bits are zero.
FACES = []
INC = [[] for _ in range(512)]
for a, b in itertools.combinations(range(9), 2):
    mask = (1 << a) | (1 << b)
    for x in range(512):
        if x & mask:
            continue
        face = frozenset([x, x | (1 << a), x | (1 << b), x | mask])
        FACES.append(face)
        for q in face:
            INC[q].append(face)
assert len(FACES) == len(set(FACES)) == 4608
assert all(len(fs) == 36 for fs in INC)

def actual_shares(S, C):
    result = []
    for c in C:
        value = 0
        for q in NB[c]:
            degree = len(NB[q] & S)
            empty = sum(not (f & S) for f in INC[q])
            value += 12 * empty // degree if degree else 0
        result.append(value)
    return result

source = ROOT / 'milestones/57-replacement-share-family/combined'
geometry = read(HERE / 'data/forced-geometry.json')
base_meta = read(source / 'data/model.json')
assert [r['directions'] for r in geometry['patterns']] == base_meta['extensions']
assert len(geometry['patterns']) == 132
# Independently enumerate all first-occurrence-normalized induced eight-step words.
def extend(word=(), vertices=(0,)):
    if len(word) == 8:
        yield word
        return
    for d in range(min(9, max(word, default=-1) + 2)):
        q = vertices[-1] ^ (1 << d)
        if q in vertices or any((q ^ old).bit_count() == 1 for old in vertices[:-1]):
            continue
        yield from extend(word + (d,), vertices + (q,))
assert set(extend()) == {tuple(r['directions']) for r in geometry['patterns']}
geom_checks = []
for row in geometry['patterns']:
    W = path(row['directions']); selected = set(W)
    assert len(W) == len(selected) == 9
    assert all((W[i] ^ W[j]).bit_count() != 1 for i in range(9) for j in range(i + 2, 9))
    saturated = {x for x in selected if len(NB[x] & selected) == 2}
    assert saturated == set(W[1:-1])
    # Definition by a contradiction witness, independently of the generating union.
    D = {q for q in range(512) if any(len(NB[x] & (selected | {q})) >= 3 for x in selected)}
    assert D.isdisjoint(selected)
    assert sorted(D) == row['forced_absent']
    C = W[3:8]
    assert C == row['centres']
    U = set(range(512)) - D
    assert selected <= U
    terms = []
    for c in C:
        for q in sorted(NB[c]):
            empty = [sorted(f) for f in INC[q] if f <= D]
            upper = len(NB[q] & U)
            assert 1 <= len(NB[q] & selected) <= upper
            credit = 12 * len(empty) // upper
            if credit:
                terms.append((c, q, tuple(sorted(map(tuple, empty))), upper, credit))
    given = [(t['centre'], t['corner'], tuple(sorted(map(tuple, t['forced_empty_faces']))), t['degree_upper'], t['credit']) for t in row['terms']]
    assert sorted(terms) == sorted(given)
    total = sum(t[-1] for t in terms)
    assert total == row['share_lower'] == sum(actual_shares(U, C))
    # Two concrete extensions at opposite ends of this inclusion interval.
    assert total <= sum(actual_shares(selected, C))
    geom_checks.append(dict(directions=row['directions'], forced_absent=len(D), lower=total))

models = {}
def load_model(folder):
    md = read(folder / 'data/model.json')
    with np.load(folder / 'build/graph.npz') as z:
        arrays = {k: z[k] for k in z.files}
    assert set(arrays) == set(md['arrays_sha256'])
    for k, h in md['arrays_sha256'].items():
        assert sha(arrays[k].tobytes()) == h
    return md, arrays
base_meta, base = load_model(source)
windows = read(HERE / 'data/windows.json')
selection = read(HERE / 'data/selected-candidate.json')
assert selection['selected'] == [1]
for name, prior in [('candidate', 'base'), ('geometry', 'base'), ('geometry-candidate', 'candidate')]:
    md, a = load_model(HERE / name)
    old = base if prior == 'base' else models[prior][1]
    assert md['extensions'] == base_meta['extensions']
    assert set(a) == set(old)
    for k in a:
        if k != 'share_lower':
            assert np.array_equal(a[k], old[k]), (name, k)
    expected = old['share_lower'].copy()
    if name == 'candidate':
        for chosen in selection['selected']:
            r = windows[chosen]
            for ds, counts in [(r['directions'],r['counts']), (r['directions'][::-1],r['counts'][::-1])]:
                shape = canon(ds)
                for di, ext in enumerate(md['extensions']):
                    if canon(ext[-6:]) == shape:
                        ix = (a['direction'] == di) & (a['count_code'] % (6**5) == encode(counts))
                        expected[ix] = np.maximum(expected[ix], 96)
        assert int((expected > old['share_lower']).sum()) == selection['strengthened_transitions']
    else:
        lower = np.array([r['lower'] for r in geom_checks], dtype=expected.dtype)
        expected = np.maximum(expected, lower[a['direction']])
        assert int((expected > old['share_lower']).sum()) == md['strengthened_transitions']
    assert np.array_equal(expected, a['share_lower'])
    r = read(HERE / name / 'data/analysis-share.json')
    raw = gzip.decompress((HERE / name / 'data/potential-share.i64.gz').read_bytes())
    assert sha(raw) == r['potential_sha256']
    pi = np.frombuffer(raw, dtype='<i8')
    mean = Fraction(r['integer_weight_mean']); p, d = mean.numerator, mean.denominator
    weights = 120 * a['count'].astype(np.int64) + a['share_lower']
    slack = d * weights + pi[a['U']] - pi[a['V']] - p
    assert np.all(slack >= 0)
    assert len(pi) == r['states'] and len(weights) == r['edges']
    span = int(pi.max()) - int(pi.min())
    assert span == r['potential_range']
    for j, edge in enumerate(r['cycle']):
        di = md['extensions'].index(edge['directions'])
        code = encode(edge['counts'])
        hits = np.flatnonzero((a['direction'] == di) & (a['count_code'] == code))
        assert len(hits) == 1
        i = hits[0]
        assert edge['state'] == int(a['U'][i])
        assert edge['next_state'] == int(a['V'][i]) == r['cycle'][(j+1) % len(r['cycle'])]['state']
        assert edge['weight'] == int(weights[i]) and edge['share_lower'] == int(a['share_lower'][i])
        assert slack[i] == 0
    assert Fraction(sum(e['weight'] for e in r['cycle']), len(r['cycle'])) == mean
    bound = Fraction(1099800*d + 7*p + span, p + 4200*d)
    assert str(bound) == r['conditional_edge_bound']
    assert bound.numerator // bound.denominator == r['conditional_integer_bound']
    assert str(mean / 120) == r['normalized_charge_mean']
    result = dict(name=name, states=len(pi), edges=len(weights), normalized_mean=str(mean/120), potential_range=span,
                  checked_inequalities=len(slack), cycle_length=len(r['cycle']),
                  cycle_share=sum(e['share_lower'] for e in r['cycle']), conditional_edge_bound=str(bound),
                  conditional_integer_bound=bound.numerator // bound.denominator,
                  strengthened_transitions=int((expected > old['share_lower']).sum()), potential_sha256=sha(raw))
    models[name] = (result, a)

controls = []
statuses = collections.Counter()
for i, r in enumerate(windows):
    c = read(HERE / f'data/controls/w{i:02d}.json')
    screen = read(HERE / f'data/screen/w{i:02d}.json'); statuses[screen['status']] += 1
    assert c['status'] == 'SAT'
    S = set(c['selected']); W = path(r['directions'])
    B = {q for q in range(512) if min((q ^ x).bit_count() for x in W[1:-1]) <= 4}
    assert set(W) <= S <= B
    degrees = {q: len(NB[q] & S) for q in S}
    assert all(deg <= 2 for deg in degrees.values())
    inside = {q for q in S if NB[q] <= B}
    assert all(degrees[q] >= 1 for q in inside)
    assert sum(degrees[q] == 1 for q in inside) <= 2
    remaining = set(S)
    while remaining:
        seed = remaining.pop(); component = {seed}; queue = [seed]
        while queue:
            for q in NB[queue.pop()] & remaining:
                remaining.remove(q); component.add(q); queue.append(q)
        assert sum(degrees[q] for q in component) == 2 * (len(component)-1)
    alpha = [sum((f & S) == {q} for f in INC[q]) for q in W[1:-1]]
    shares = actual_shares(S, W[1:-1])
    assert alpha == c['census']['alpha'] and shares == c['census']['share']
    assert all(6 <= a <= 21 if b == 6 else a == b for a, b in zip(alpha, r['counts']))
    controls.append(dict(window=i, total_share=sum(shares)))
assert dict(statuses) == {'INFEASIBLE':1, 'UNKNOWN':11}
generalized = {p.name:read(p)['status'] for p in sorted((HERE / 'data/generalized').glob('*.json'))}
assert len(generalized) == 6 and set(generalized.values()) == {'UNKNOWN'}

# Compare geometric credit with each saved predecessor bottleneck cycle.
cycle_comparisons = []
lookup = {tuple(r['directions']):r['lower'] for r in geom_checks}
for entry in geometry['cycle_comparisons']:
    r = read(ROOT / entry['source'] / 'data/analysis-share.json')
    credits = [lookup[tuple(e['directions'])] for e in r['cycle']]
    assert credits == entry['credits'] and sum(credits) == entry['total'] and len(credits) == entry['cycle_length']
    cycle_comparisons.append(entry)
# Independently identify the complete tight cyclic family using reachability and
# an acyclic condensation check, rather than the producer's SCC algorithm.
family = read(HERE / 'data/critical-family.json')
critical_edges = read(HERE / 'data/critical-edges.json')
source_analysis = read(source / 'data/analysis-share.json')
raw = gzip.decompress((source / 'data/potential-share.i64.gz').read_bytes())
assert sha(raw) == source_analysis['potential_sha256'] == family['source_potential_sha256']
pi = np.frombuffer(raw, dtype='<i8')
mean = Fraction(source_analysis['integer_weight_mean'])
slack = mean.denominator * (120*base['count'].astype(np.int64)+base['share_lower']) + pi[base['U']] - pi[base['V']] - mean.numerator
assert np.all(slack >= 0)
tight = np.flatnonzero(slack == 0)
adj = collections.defaultdict(set); rev = collections.defaultdict(set)
for u, v in zip(base['U'][tight].tolist(), base['V'][tight].tolist()):
    adj[u].add(v); rev[v].add(u)
def reachable(graph, root):
    seen = {root}; stack = [root]
    while stack:
        for v in graph[stack.pop()]:
            if v not in seen:
                seen.add(v); stack.append(v)
    return seen
def acyclic(pairs, vertices=None):
    pairs = set(pairs)
    vertices = set(vertices or ()) | {u for u,v in pairs} | {v for u,v in pairs}
    degree = collections.Counter(v for u,v in pairs)
    graph = collections.defaultdict(list)
    for u,v in pairs: graph[u].append(v)
    queue = collections.deque(v for v in vertices if degree[v] == 0)
    visited = set()
    while queue:
        u = queue.popleft(); visited.add(u)
        for v in graph[u]:
            degree[v] -= 1
            if degree[v] == 0: queue.append(v)
    return visited == vertices
nodes = {e['u'] for e in critical_edges} | {e['v'] for e in critical_edges}
remaining = set(nodes); components = []
while remaining:
    root = min(remaining)
    component = reachable(adj, root) & reachable(rev, root)
    assert component <= remaining
    components.append(component); remaining -= component
assert len(components) == 2 and all(len(c) == 12 for c in components)
component_of = {v:min(c) for c in components for v in c}
condensed = set(); cyclic_ids = set()
for i in tight:
    u,v = int(base['U'][i]),int(base['V'][i])
    if u in component_of and v in component_of and component_of[u] == component_of[v]:
        cyclic_ids.add(int(i))
    else:
        condensed.add((component_of.get(u,u),component_of.get(v,v)))
assert acyclic(condensed)
assert cyclic_ids == {e['source_edge'] for e in critical_edges}
assert len(cyclic_ids) == 32 and len(nodes) == 24 and len(windows) == 12
assert all(sum(int(base['U'][i]) in c for i in cyclic_ids) == 16 for c in components)
for e in critical_edges:
    i = e['source_edge']; assert e['u'] == int(base['U'][i]) and e['v'] == int(base['V'][i])
    assert base['share_lower'][i] == 0
    ds = base_meta['extensions'][int(base['direction'][i])][-6:]
    cs = tuple(int(base['count_code'][i]) // (6**j) % 6 + 1 for j in range(4,-1,-1))
    key = min((canon(ds),cs),(canon(ds[::-1]),cs[::-1]))
    w = windows[e['window']]
    assert key == (tuple(w['directions']),tuple(w['counts']))
for i,w in enumerate(windows):
    occurrences = [e for e in critical_edges if e['window'] == i]
    assert len(occurrences) == w['occurrences']
    assert len({component_of[e['u']] for e in occurrences}) == len(w['components']) == 2
covers = [i for i in range(12) if acyclic([(e['u'],e['v']) for e in critical_edges if e['window'] != i],nodes)]
assert covers == read(HERE / 'data/priorities.json')['single_pattern_cycle_covers'] == list(range(12))
critical_check = dict(states=24, edges=32, components=[dict(states=12,edges=16) for _ in components],
                      windows=12, single_pattern_covers=covers, source_potential_inequalities=len(slack))

# Positive controls on every oriented eight-step window of the published bank.
bank_path = ROOT / 'work/bank9.json'
bank = read(bank_path); assert len(bank) == 131
bank_windows = 0; positive_windows = 0; minimum_margin = None
seen_shapes = set()
for row in bank:
    W = row['vertex_sequence']; S = set(W)
    assert len(W) == len(S) and all(0 <= v < 512 for v in W)
    assert all((W[i]^W[i+1]).bit_count() == 1 for i in range(len(W)-1))
    assert all((W[i]^W[j]).bit_count() != 1 for i in range(len(W)) for j in range(i+2,len(W)))
    empty_at = [0]*512
    for f in FACES:
        if not (f & S):
            for q in f: empty_at[q] += 1
    degree = [len(NB[q]&S) for q in range(512)]
    share_at = {v:sum(12*empty_at[q]//degree[q] for q in NB[v]) for v in S}
    for oriented in [W, W[::-1]]:
        directions = [(oriented[i]^oriented[i+1]).bit_length()-1 for i in range(len(oriented)-1)]
        for r in range(len(directions)-7):
            shape = canon(directions[r:r+8]); lower = lookup[shape]
            actual = sum(share_at[v] for v in oriented[r+3:r+8])
            assert lower <= actual
            bank_windows += 1; positive_windows += lower > 0; seen_shapes.add(shape)
            margin = actual - lower
            minimum_margin = margin if minimum_margin is None else min(minimum_margin,margin)
bank_check = dict(paths=131, oriented_windows=bank_windows, positive_credit_windows=positive_windows,
                  occurring_shapes=len(seen_shapes), minimum_share_margin=minimum_margin, input_sha256=sha(bank_path.read_bytes()))

# Independently recompute the six simplex features of the fixed-weighting ceiling.
weighted = read(HERE / 'data/weighted-ceiling.json')
cycle = read(HERE / 'geometry/data/analysis-share.json')['cycle']
assert weighted['cycle_length'] == len(cycle) == len(weighted['rows']) == 20
feature_sums = [0]*6
for edge, saved in zip(cycle, weighted['rows']):
    assert edge['directions'] == saved['directions']
    W = path(edge['directions']); selected = set(W)
    D = {q for q in range(512) if any(len(NB[x] & (selected | {q})) >= 3 for x in selected)}
    individual = actual_shares(set(range(512))-D, W[3:8])
    assert individual == saved['individual']
    # Last entering count is independently read from the saved cycle word.
    base_weight = 120*edge['counts'][-1]
    assert base_weight == edge['weight'] - edge['share_lower']
    features = [edge['weight']] + [base_weight+5*g for g in individual]
    assert features == saved['vertex_weights']
    feature_sums = [a+b for a,b in zip(feature_sums,features)]
vertex_means = [Fraction(s,len(cycle)) for s in feature_sums]
assert list(map(str,vertex_means)) == weighted['simplex_vertex_means']
ceiling = max(vertex_means)
assert ceiling == Fraction(989,2)
assert str(ceiling/120) == weighted['normalized_ceiling']
# The seven lost windows retain the 7*mu term even with potential range zero.
# (A+7*mu)/(B+mu)<235 is equivalent to (235-7)*mu>A-235*B.
A,B = 1099800,4200
threshold = Fraction(A-235*B,235-7)
assert threshold == Fraction(9400,19)
assert str(threshold) == weighted['integer_weight_threshold_to_exclude_235_with_zero_potential_range']
assert ceiling < threshold and weighted['weighting_alone_cannot_exclude_235'] is True
best_saved_cycle_bound = (A+7*ceiling)/(B+ceiling)
assert best_saved_cycle_bound >= 235
weighted_check = dict(cycle_length=20, feature_sums=feature_sums, simplex_vertex_means=list(map(str,vertex_means)),
                      integer_weight_ceiling=str(ceiling), normalized_ceiling=str(ceiling/120),
                      strict_exclusion_threshold=str(threshold), threshold_gap=str(threshold-ceiling),
                      zero_potential_range_bound_at_ceiling=str(best_saved_cycle_bound),
                      scope='This fixed six-feature relaxation cannot exclude 235 with the stated seven-window boundary accounting. No claim that the saved cycle is realizable by a snake.')

out = dict(status='PASS', cube_faces=4608, shapes=132,
           positive_shapes=sum(r['lower'] > 0 for r in geom_checks), maximum_lower=max(r['lower'] for r in geom_checks),
           geometries=geom_checks, critical_family=critical_check, bank=bank_check, weighted_ceiling=weighted_check, models=[models[k][0] for k in models], controls=controls,
           screen_status=dict(statuses), generalized_status=generalized, cycle_comparisons=cycle_comparisons,
           scope='Independent finite arithmetic and geometry checks, including every edge potential inequality. No Lean audit is performed here. The inherited numerical share rules and full arbitrary-snake graph/overlap/boundary assembly remain separate obligations; no improved global bound follows from this report alone.')
(HERE / 'data/verification-geometry.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='geometries'},indent=2))
