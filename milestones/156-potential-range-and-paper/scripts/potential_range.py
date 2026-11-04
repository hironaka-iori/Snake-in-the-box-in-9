"""Exact conditional range test. Launch only through run_potential.py."""
from pathlib import Path
from fractions import Fraction
import argparse
import gc
import gzip
import hashlib
import json
import os
import shutil
import sys
import time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
sys.path.insert(0, str(R / 'work/solver_packages'))
import numpy as np
from reconstruct144 import reconstruct

FLOORS = {'012031':16,'012032':16,'012034':18,'012301':16,'012304':16,
          '012310':12,'012314':16,'012340':16,'012345':16}
BLOCK = 200000


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def array_sha(array):
    return hashlib.sha256(memoryview(np.ascontiguousarray(array)).cast('B')).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def save(path, value):
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value, indent=2)+'\n', encoding='utf-8', newline='\n')
    temporary.replace(path)


def canon(word):
    names = {}
    return ''.join(str(names.setdefault(int(x), len(names))) for x in word)


def shape(word):
    return min(canon(word), canon(word[::-1]))


def main():
    assert __debug__, 'Python optimization disables required checks'
    parser = argparse.ArgumentParser()
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--parent', type=int, required=True)
    args = parser.parse_args()
    run = args.run.resolve()
    run.relative_to(H / 'data')
    request = read(run / 'request.json')
    lock = read(R / 'work/fullgraph-active.lock')
    assert lock['parent_pid'] == args.parent == request['parent_pid']
    assert lock['run'] == str(run)
    assert os.environ.get('SNAKE156_WORKER_PARENT') == str(args.parent)
    prep = read(H / 'data/preparation.json')
    for relative, digest in prep['script_pins'].items():
        assert sha(R / relative) == digest, relative
    plan = read(R / prep['plan_path'])
    assert sha(R / prep['plan_path']) == prep['plan_sha256']
    progress = run / 'progress.json'
    save(progress, dict(phase='RECONSTRUCTING', worker_pid=os.getpid()))
    data = reconstruct(np)
    arrays, meta, ds = data['arrays'], data['meta'], data['ds']
    mask, shared, digits = data['mask'], data['shared'], data['digits']
    for relative, digest in data['pins'].items():
        assert sha(R / relative) == digest, relative
    expected = read(R / 'milestones/144-countfree-share18/data/share18-impact/results.json')
    removed_path = R / 'milestones/144-countfree-share18/data/share18-impact/removed-indices.json'
    assert np.array_equal(np.flatnonzero(~mask), np.asarray(read(removed_path)))
    assert (meta['states'], len(mask), int(mask.sum())) == (1601856, 4947008, 4661572)
    old_floor = {''.join(map(str, row['shape'])):row['share'] for row in data['completed']['countfree_floors']}
    old_floor['012034'] = 18
    direction = arrays['direction']
    shapes = [shape(word[-6:]) for word in ds]
    last = digits[:, -1].astype(np.int64)
    source_weight = arrays['weight'].astype(np.int64)
    original_floor = np.asarray([old_floor.get(s, 0) for s in shapes], dtype=np.int64)[direction]
    old144 = (np.maximum(source_weight, 120*last+original_floor)+shared)[mask]
    assert array_sha(old144) == expected['profiles'][0]['weight_sha256']
    conditional = np.asarray([FLOORS[s] for s in shapes], dtype=np.int64)[direction]
    source16 = np.maximum(source_weight, 120*last+conditional)
    saved = read(R / 'milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18.json')
    assert array_sha(source16) == saved['weight_sha256']
    matched = np.zeros(len(mask), dtype=bool)
    lo_bound = np.asarray([4, 0, 4, 0, 3])
    hi_bound = np.asarray([4, 4, 4, 5, 3])
    for index, word in enumerate(ds):
        lo, hi = np.searchsorted(direction, [index, index+1])
        five = digits[lo:hi, 1:6]
        for reverse in [False, True]:
            selected = word[-6:][::-1] if reverse else word[-6:]
            if canon(selected) != '012032':
                continue
            counts = five[:, ::-1] if reverse else five
            matched[lo:hi] |= np.all((counts >= lo_bound) & (counts <= hi_bound), axis=1)
    assert int(matched.sum()) == 156 and int(matched[mask].sum()) == 91
    assert not np.any(np.any(digits[matched, 1:6] == 6, axis=1))
    new_floor = np.maximum(conditional, np.where(matched, 17, 0))
    source17 = np.maximum(source_weight, 120*last+new_floor)
    assert np.all((source17-source16 >= 0) & (source17-source16 <= 1))
    assert not np.any((source17 != source16) & ~matched)
    ids = np.flatnonzero(mask)
    u, v = arrays['U'][mask], arrays['V'][mask]
    weights = (source17+shared)[mask]
    assert np.all(weights >= source16[mask])
    retained_matches = matched[mask]
    # Re-evaluate original row witnesses without transferring their obstruction
    # to a graph that removed their edges.
    for witness in plan['original_source_profile']['saved_row_recalculation'].values():
        for row in witness['rows']:
            index = row['edge']
            assert int(arrays['U'][index]) == row['u'] and int(arrays['V'][index]) == row['v']
            assert ds[int(direction[index])] == row['directions']
            assert digits[index].tolist() == row['counts']
            assert int(source16[index]) == row['floor16_weight']
            assert int(source17[index]) == row['floor17_weight']
            assert bool(matched[index]) == row['share17_match']
    fourteen = plan['fourteen_cycle']['rows']
    for row in fourteen:
        index = row['edge']
        assert mask[index] and int(arrays['U'][index]) == row['u'] and int(arrays['V'][index]) == row['v']
        assert ds[int(direction[index])] == row['directions'] and digits[index].tolist() == row['counts']
        assert int(source17[index]+shared[index]) == row['conditional_weight']
        assert not matched[index]
    assert sum(row['conditional_weight'] for row in fourteen) == 6944
    assert 2*496-sum(row['conditional_weight'] for row in fourteen[:2]) == 480
    eleven = plan['original_source_profile']['saved_row_recalculation']['eleven_cycle']['rows']
    assert all(mask[row['edge']] for row in eleven)
    assert sum(int(source17[row['edge']]+shared[row['edge']]) for row in eleven) == 5458
    build = dict(states=meta['states'], source_edges=len(mask), retained_edges=len(ids),
        old144_weight_sha256=array_sha(old144), source16_weight_sha256=array_sha(source16),
        source17_weight_sha256=array_sha(source17), weight_sha256=array_sha(weights),
        retained_row_ids_sha256=array_sha(ids), source_suffix_matches=int(matched.sum()),
        retained_suffix_matches=int(retained_matches.sum()),
        changed_source_share17_rows=int(np.count_nonzero(source17 != source16)),
        changed_retained_share17_rows=int(np.count_nonzero((source17 != source16) & mask)),
        fourteen_cycle_total=6944, eleven_cycle_total=5458, range_lower_bound_at496=480)
    save(run / 'graph-reconstruction.json', build)
    n = meta['states']
    del data, arrays, meta, direction, mask, shared, digits, source_weight, source16, source17
    del matched, last, conditional, new_floor, original_floor, old144
    gc.collect()
    archive = R / 'milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum' / saved['potential_file']
    raw = gzip.decompress(archive.read_bytes())
    assert hashlib.sha256(raw).hexdigest() == saved['potential_sha256']
    baseline = np.frombuffer(raw, dtype='<i8')
    assert len(baseline) == n and int(baseline.min()) == 0 and int(baseline.max()) == 602

    def scan(potential):
        minimum = None
        for lo in range(0, len(weights), BLOCK):
            hi = min(lo+BLOCK, len(weights))
            slack = weights[lo:hi]+potential[u[lo:hi]]-potential[v[lo:hi]]-496
            value = int(slack.min())
            minimum = value if minimum is None else min(minimum, value)
        assert minimum is not None and minimum >= 0
        return minimum

    baseline_slack = scan(baseline)
    save(run / 'baseline-certificate.json', dict(status='PASS_ALL_RETAINED_NEW_WEIGHTS',
        mean=496, range=602, minimum_slack=baseline_slack, inequalities=len(weights),
        source_archive=str(archive), source_archive_sha256=sha(archive),
        raw_potential_sha256=saved['potential_sha256'], weight_sha256=build['weight_sha256']))
    journal = run / 'journal'; journal.mkdir()
    layers = []
    journal_bytes = 0
    maximum_journal = 2*1024**3
    assert n < 2**32 and len(weights) < 2**32
    assert 1503*(496+max(abs(int(weights.min())), abs(int(weights.max())))) < 2**62
    started = time.monotonic()
    deadline = started+600
    dist = np.zeros(n, dtype=np.int64)
    status = 'UNRESOLVED_ITERATION_LIMIT'
    selected = baseline
    selected_range = 602
    endpoint = None
    for iteration in range(1, 1501):
        if time.monotonic() >= deadline:
            status = 'UNRESOLVED_TIME_LIMIT'; break
        save(progress, dict(phase='DISCOVERY', worker_pid=os.getpid(), iteration=iteration,
            discovery_started=started, journal_bytes=journal_bytes, maximum_deficit=-int(dist.min())))
        nxt = dist.copy()
        for lo in range(0, len(weights), BLOCK):
            hi = min(lo+BLOCK, len(weights))
            np.minimum.at(nxt, v[lo:hi], dist[u[lo:hi]]+weights[lo:hi]-496)
        if np.array_equal(nxt, dist):
            assert int(dist.max()) == 0
            selected_range = -int(dist.min())
            assert 480 <= selected_range <= 602
            selected = dist+selected_range
            endpoint = int(np.argmin(dist))
            status = 'PASS_MINIMUM_RANGE_AT_MEAN496'; break
        changed = np.flatnonzero(nxt < dist)
        needed = len(changed)*8
        if journal_bytes+needed > maximum_journal or shutil.disk_usage(run).free < needed+512*1024**2:
            status = 'UNRESOLVED_JOURNAL_LIMIT'; break
        predecessor = np.full(n, -1, dtype=np.int64)
        for lo in range(0, len(weights), BLOCK):
            hi = min(lo+BLOCK, len(weights))
            candidate = dist[u[lo:hi]]+weights[lo:hi]-496
            eligible = np.flatnonzero((candidate == nxt[v[lo:hi]]) & (nxt[v[lo:hi]] < dist[v[lo:hi]]))
            np.maximum.at(predecessor, v[lo:hi][eligible], eligible+lo)
        assert np.all(predecessor[changed] >= 0)
        pairs = np.column_stack([changed, predecessor[changed]]).astype('<u4')
        path = journal / ('layer-'+str(iteration).zfill(4)+'.u32')
        pairs.tofile(path)
        assert path.stat().st_size == needed
        layers.append(dict(path=path.relative_to(run).as_posix(), rows=len(changed), sha256=sha(path)))
        journal_bytes += needed
        del predecessor, pairs, changed
        dist = nxt
        deficit = -int(dist.min())
        assert deficit <= 602, 'Verified baseline contradicts the derived path deficit'
        if deficit == 602:
            endpoint = int(np.argmin(dist))
            status = 'PASS_MINIMUM_RANGE_AT_MEAN496'; break
    discovery_seconds = time.monotonic()-started
    save(progress, dict(phase='FINALIZING', worker_pid=os.getpid(),
        discovery_started=started, discovery_seconds=discovery_seconds, status=status))
    witness = []
    if endpoint is not None:
        vertex = endpoint
        for layer in reversed(layers):
            path = run / layer['path']
            assert sha(path) == layer['sha256']
            pairs = np.memmap(path, dtype='<u4', mode='r', shape=(layer['rows'], 2))
            index = int(np.searchsorted(pairs[:, 0], vertex))
            if index < len(pairs) and int(pairs[index, 0]) == vertex:
                edge = int(pairs[index, 1])
                assert int(v[edge]) == vertex
                witness.append(edge)
                vertex = int(u[edge])
            del pairs
        witness.reverse()
        assert all(int(v[a]) == int(u[b]) for a,b in zip(witness, witness[1:]))
        assert 496*len(witness)-sum(int(weights[e]) for e in witness) == selected_range
    slack = scan(selected)
    output = run / 'potential.i64.gz'
    potential_raw = selected.astype('<i8').tobytes()
    output.write_bytes(gzip.compress(potential_raw, mtime=0))
    for relative, digest in prep['input_pins'].items():
        assert sha(R / relative) == digest, relative
    for relative, digest in request['completion_pins'].items():
        assert sha(R / relative) == digest, relative
    result = dict(status=status, graph=build, mean=496, occurrence_credit=0,
        potential_range=selected_range, fixed_mean_minimal=status.startswith('PASS_MINIMUM'),
        range_improved=selected_range < 602, certified_range_lower_bound=selected_range if witness else 480,
        comparison=str(Fraction(1098960+8*496+selected_range, 4696)),
        conditional234_margin=632-selected_range, all_edge_inequalities_checked=len(weights),
        minimum_slack=slack, potential_file=output.name, potential_sha256=hashlib.sha256(potential_raw).hexdigest(),
        potential_archive_sha256=sha(output), iterations=iteration, discovery_seconds=discovery_seconds,
        journal_bytes=journal_bytes, journal=layers,
        deficit_walk=[dict(source_edge=int(ids[e]),u=int(u[e]),v=int(v[e]),weight=int(weights[e]),
                           share17_match=bool(retained_matches[e])) for e in witness],
        floors=FLOORS, pending_floors=plan['pending_floors'], inherited_assumptions=plan['inherited_assumptions'],
        preparation_sha256=sha(H/'data/preparation.json'), execution_request_sha256=sha(run/'request.json'),
        completion_pins=request['completion_pins'], input_pins=prep['input_pins'],
        joint_slope_range_optimality=False, new_global_bound=False, Lean_edge_certificate_complete=False,
        scope='Exact finite graph under all listed conditional floors, count, six-floor, reference and interpretation premises. No actual-snake upper bound or new Lean proof.')
    save(run / 'result.json', result)
    save(progress, dict(phase='FINISHED', worker_pid=os.getpid(), status=status))
    print(json.dumps({key:result[key] for key in ['status','mean','potential_range','range_improved',
        'comparison','discovery_seconds','new_global_bound']}), flush=True)


if __name__ == '__main__':
    main()
