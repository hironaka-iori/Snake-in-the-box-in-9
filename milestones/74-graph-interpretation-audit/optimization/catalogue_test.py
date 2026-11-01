"""Exact finite-graph tests for weakening one conditional share rule.

This supplies graph witnesses, never an arbitrary-snake interpretation.
Run without arguments to discover witnesses; --verify checks saved witnesses.
"""
from pathlib import Path
import gzip
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OLD = ROOT / 'milestones/72-four-count-proof-closure/critical-current'
sys.path.insert(0, str(ROOT / 'work/solver_packages'))
import numpy as np

DATA = HERE / 'data'
DATA.mkdir(exist_ok=True)
read = lambda p: json.loads(p.read_text())
sha = lambda b: hashlib.sha256(b).hexdigest()
PREFIX = 'countfree16-all-except012034x20-except012310x12'
SHAPES = ['012031', '012032', '012034', '012301', '012304',
          '012310', '012314', '012340', '012345']
FLOORS = [16, 16, 20, 16, 16, 12, 16, 16, 16]
# Retain the already checked weaker distinct-direction bound in case 8.
TESTS = [(3, 0), (1, 0), (2, 0), (5, 0), (7, 0), (8, 12)]


def canon(word):
    labels = {}
    return ''.join(str(labels.setdefault(x, len(labels))) for x in word)


def setup():
    meta = read(OLD / 'data/source-proved-model.json')
    with np.load(OLD / 'build/source-graph.npz') as z:
        a = {k: z[k] for k in z.files}
    for k, expected in meta['arrays_sha256'].items():
        assert sha(a[k].tobytes()) == expected, k
    extensions = read(ROOT / 'milestones/59-extended-share-window/extended/data/model.json')['extensions']
    shape_of_direction = np.array([
        SHAPES.index(min(canon(ds[-6:]), canon(ds[-6:][::-1])))
        for ds in extensions], dtype=np.int8)
    shape = shape_of_direction[a['direction']]
    entering = 120 * (a['count_code'].astype(np.int64) % 6 + 1)
    full = np.maximum(a['weight'], entering + np.array(FLOORS)[shape])
    with np.load(OLD / f'build/{PREFIX}-graph.npz') as z:
        for key in ['U', 'V', 'direction', 'count_code', 'history']:
            assert np.array_equal(a[key], z[key]), key
        assert np.array_equal(full, z['weight'])
    cycle = [r['edge'] for r in read(OLD / f'data/{PREFIX}-analysis.json')['cycle']]
    return meta, a, shape, entering, full, cycle


def weights(a, shape, entering, full, index, floor):
    w = full.copy()
    selected = shape == index
    w[selected] = np.maximum(a['weight'][selected], entering[selected] + floor)
    return w


def edge_rows(edges, a, shape, w):
    return [dict(edge=int(e), u=int(a['U'][e]), v=int(a['V'][e]),
                 weight=int(w[e]), base_weight=int(a['weight'][e]),
                 shape=SHAPES[int(shape[e])], count_code=int(a['count_code'][e]),
                 direction=int(a['direction'][e]), history=int(a['history'][e]))
            for e in edges]


def verify_walk(rows, a, shape, w, closed=False):
    edges = [r['edge'] for r in rows]
    assert rows == edge_rows(edges, a, shape, w)
    assert all(rows[i]['v'] == rows[i+1]['u'] for i in range(len(rows)-1))
    if closed:
        assert rows and rows[-1]['v'] == rows[0]['u']
    return len(rows), sum(r['weight'] for r in rows)


def run():
    meta, a, shape, entering, full, cycle = setup()
    U, V, N = a['U'], a['V'], meta['states']
    results = []
    for index, floor in TESTS:
        started = time.monotonic()
        w = weights(a, shape, entering, full, index, floor)
        cyc = edge_rows(cycle, a, shape, w)
        length, total = verify_walk(cyc, a, shape, w, closed=True)
        assert total == 496 * length
        dist = np.zeros(N, dtype=np.int64)
        parents = []
        result = dict(shape=SHAPES[index], weakened_floor=floor,
                      source_arrays_sha256=meta['arrays_sha256'],
                      weight_sha256=sha(w.tobytes()), cycle=cyc,
                      changed_edges=int(np.sum(w != full)), slope=496)
        for iteration in range(1, 228):
            candidate = dist[U] + w - 496
            nxt = dist.copy()
            np.minimum.at(nxt, V, candidate)
            if np.array_equal(nxt, dist):
                potential = dist - dist.min()
                assert np.all(496 + potential[V] <= w + potential[U])
                result.update(status='SUFFICIENT_CONDITIONAL_CATALOGUE',
                              potential_range=int(potential.max()),
                              exclusion_margin=632-int(potential.max()))
                assert result['exclusion_margin'] > 0
                raw = potential.astype('<i8').tobytes()
                result['potential_sha256'] = sha(raw)
                (DATA / f'weaken-{SHAPES[index]}.i64.gz').write_bytes(gzip.compress(raw, mtime=0))
                break
            eligible = np.flatnonzero((candidate == nxt[V]) & (nxt[V] < dist[V]))
            parent = np.full(N, -1, dtype=np.int32)
            np.maximum.at(parent, V[eligible], eligible)
            assert np.all(parent[nxt < dist] >= 0)
            parents.append(parent)
            dist = nxt
            minimum = int(dist.min())
            if minimum <= -632:
                endpoint = int(np.argmin(dist))
                edges = []
                for layer in reversed(parents):
                    e = int(layer[endpoint])
                    if e >= 0:
                        edges.append(e)
                        endpoint = int(U[e])
                edges.reverse()
                rows = edge_rows(edges, a, shape, w)
                length, total = verify_walk(rows, a, shape, w)
                deficit = 496 * length - total
                assert length <= iteration <= 227 and deficit >= 632
                assert -deficit == minimum
                result.update(status='ALL_CONSTANT_SLOPE_RANGE_CERTIFICATES_OBSTRUCTED',
                              walk=rows, length=length, total_weight=total, deficit=deficit)
                break
        else:
            result['status'] = 'INCONCLUSIVE_AFTER_227_ITERATIONS'
        result.update(iterations=iteration, seconds=time.monotonic()-started)
        results.append(result)
        (DATA / f'weaken-{SHAPES[index]}.json').write_text(json.dumps(result, indent=2)+'\n')
        print({k: v for k, v in result.items() if k in
               ['shape', 'status', 'length', 'deficit', 'potential_range', 'iterations', 'seconds']}, flush=True)
    out = dict(status='EXACT_FINITE_GRAPH_CATALOGUE_TESTS', tests=results,
               full_floors=dict(zip(SHAPES, FLOORS)),
               scope='All other mixed-catalogue floors are retained, including unproved premises. '
                     'An obstruction concerns constant-slope potentials with a global range and '
                     'the current boundary budget on this exact relaxed graph only. '
                     'It does not rule out stronger geometry, reachable-state restrictions, '
                     'different boundary estimates or a smaller actual-snake upper bound.')
    (DATA / 'catalogue-tests.json').write_text(json.dumps(out, indent=2)+'\n')


def verify():
    meta, a, shape, entering, full, _ = setup()
    receipt = read(DATA / 'catalogue-tests.json')
    assert receipt['full_floors'] == dict(zip(SHAPES, FLOORS))
    assert [(r['shape'], r['weakened_floor']) for r in receipt['tests']] == [(SHAPES[i], f) for i, f in TESTS]
    checked = []
    for r in receipt['tests']:
        index = SHAPES.index(r['shape'])
        w = weights(a, shape, entering, full, index, r['weakened_floor'])
        assert r['source_arrays_sha256'] == meta['arrays_sha256']
        assert r['weight_sha256'] == sha(w.tobytes())
        n, total = verify_walk(r['cycle'], a, shape, w, closed=True)
        assert total == 496*n
        if r['status'] == 'ALL_CONSTANT_SLOPE_RANGE_CERTIFICATES_OBSTRUCTED':
            n, total = verify_walk(r['walk'], a, shape, w)
            assert n == r['length'] <= 227
            assert total == r['total_weight']
            assert 496*n-total == r['deficit'] >= 632
        elif r['status'] == 'SUFFICIENT_CONDITIONAL_CATALOGUE':
            raw = gzip.decompress((DATA / f"weaken-{r['shape']}.i64.gz").read_bytes())
            assert sha(raw) == r['potential_sha256']
            pi = np.frombuffer(raw, dtype='<i8')
            assert len(pi) == meta['states'] and pi.min() == 0
            assert pi.max() == r['potential_range'] <= 631
            assert np.all(496+pi[a['V']] <= w+pi[a['U']])
        else:
            raise AssertionError('No decisive witness for '+r['shape'])
        checked.append(dict(shape=r['shape'], status=r['status']))
    output = dict(status='PASS_EXACT_GRAPH_WITNESSES', results=checked,
                  input_sha256=sha((DATA / 'catalogue-tests.json').read_bytes()),
                  verifier_sha256=sha(Path(__file__).read_bytes()),
                  scope='Exact array and path/potential validation in Python; no full Lean graph interpretation or numerical snake theorem.')
    (DATA / 'verification.json').write_text(json.dumps(output, indent=2)+'\n')
    print(output['status'], len(checked), 'tests', flush=True)


if __name__ == '__main__':
    verify() if '--verify' in sys.argv else run()
