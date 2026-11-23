"""Search for an induced path with a canonical direction-count profile."""
import argparse
import gzip
import json
import subprocess
from itertools import combinations
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import read_path
from q9_modular_orientation import modular
from q9_square_census import add_popcount


def append_upper_bound(f, bits, bound, guard=()):
    """Under the negation of guard, enforce the binary number <= bound."""
    prefix_mismatch = list(guard)
    for i in reversed(range(len(bits))):
        bit = bits[i]
        if bound >> i & 1:
            prefix_mismatch.append(-bit)
        else:
            f.append([*prefix_mismatch, -bit])


def append_order(f, pool, left, right):
    prefix_mismatch = []
    for a, b in reversed(list(zip(left, right))):
        f.append([*prefix_mismatch, -a, b])
        equal = pool.id()
        f.extend([[*prefix_mismatch, a, b, equal],
                  [*prefix_mismatch, -a, -b, equal]])
        prefix_mismatch = [-equal]


def build(dim, length, distance, tight_pair=False, prefix_cuts=(), column_cuts=False, axis_windows=(), include_rank=True):
    rank_bits = max(1, length.bit_length() - 1)
    if include_rank:
        f, end = modular(dim,length,distance,rank_bits,anchor_distances=True,
                         prefix_cuts=prefix_cuts,axis_windows=axis_windows)
    else:
        assert not prefix_cuts and not axis_windows
        from q9_endpoint_distance_bound import build as degree_formula
        f, end = degree_formula(dim,length,distance,include_rank=False)
    pool = IDPool(start_from=f.nv + 1)
    counts,_ = add_frequencies(f,pool,dim,length,distance,tight_pair)
    if column_cuts:
        from q9_projected_column_cuts import add_column_cuts
        add_column_cuts(f, pool, counts, end, length, range(dim))
    return f, end, counts


def add_frequencies(f, pool, dim, length, distance, tight_pair=False, ordered=True):
    physical = []
    counts = []
    for axis in range(dim):
        mask = 1 << axis
        bonds = []
        for u in range(1 << dim):
            if u & mask:
                continue
            v = u ^ mask
            bond = pool.id()
            f.extend([[-bond, u+1], [-bond, v+1], [bond, -u-1, -v-1]])
            bonds.append(bond)
            physical.append((u,v,bond))
        bits = add_popcount(f, pool, [bonds])
        assert all(bit is not None for bit in bits)
        counts.append(bits)
        f.append([bits[0] if axis < distance else -bits[0]])
        append_upper_bound(f, bits, (length+2)//3)
        if (dim, length) == (9, 221):
            # At most two crossings in any direction would imply <=210 edges.
            append_upper_bound(f, [-bit for bit in bits], (1 << len(bits))-1-3)
        if ordered and axis not in (0, distance):
            append_order(f, pool, counts[axis-1], bits)

    if (dim, length) == (9, 221):
        # After sorting within parity blocks, checking the minimum pair
        # of each parity type enforces the inequality for all 36 pairs.
        pairs = []
        if ordered:
            if distance >= 2:
                pairs.append((0, 1, 18))
            if dim-distance >= 2:
                pairs.append((distance, distance+1, 18))
            if distance < dim:
                pairs.append((0, distance, 17))
        else:
            pairs = [(a,b,18 if (a<distance)==(b<distance) else 17)
                     for a,b in combinations(range(dim),2)]
        thresholds = {}
        for a, b, minimum in pairs:
            for i in range(1, minimum+1):
                clause = []
                for axis, value in ((a, i), (b, minimum+1-i)):
                    if (axis, value) not in thresholds:
                        indicator = pool.id()
                        thresholds[axis, value] = indicator
                        bits = counts[axis]
                        append_upper_bound(
                            f, [-bit for bit in bits],
                            (1 << len(bits))-1-value, [-indicator],
                        )
                    clause.append(thresholds[axis, value])
                f.append(clause)
    if tight_pair:
        assert ordered and (dim, length) == (9, 221) and distance < dim
        columns = [list(column) for column in zip(counts[0], counts[distance])]
        minimum_mixed_pair = add_popcount(f, pool, columns)
        assert all(bit is not None for bit in minimum_mixed_pair)
        append_upper_bound(f, minimum_mixed_pair, 17)
    return counts,physical


def profile(path, dim):
    counts = [0]*dim
    for u, v in zip(path, path[1:]):
        counts[(u ^ v).bit_length()-1] += 1
    return counts


def control():
    with gzip.open('q9_port_followup_public191.txt.gz', 'rt') as source:
        sample = list(map(int, next(source).split()))
    first, last = sample[0], sample[-1]
    delta = first ^ last
    original_counts = profile(sample, 9)
    order = sorted(range(9), key=lambda a: (not (delta >> a & 1), original_counts[a]))
    path = [sum((((v ^ first) >> a) & 1) << i for i, a in enumerate(order))
            for v in sample]
    f, end, bits = build(9, len(path)-1, delta.bit_count())
    selected = set(path)
    f.extend([[v+1 if v in selected else -v-1] for v in range(512)])
    with Cadical195(bootstrap_with=f) as solver:
        assert solver.solve()
        model = solver.get_model()
        assert read_path(model, 9, len(path)-1, end) == path
        actual = [sum((model[bit-1] > 0) << i for i, bit in enumerate(row)) for row in bits]
        assert actual == profile(path, 9)
    print(json.dumps(dict(status='CONTROL_OK', length=len(path)-1,
                          distance=delta.bit_count(), counts=actual)), flush=True)


def search(distance, budget, checker, out, tight_pair):
    f, end, _ = build(9, 221, distance, tight_pair=tight_pair)
    header = dict(distance=distance, budget=budget, tight_pair=tight_pair,
                  variables=f.nv, clauses=len(f.clauses))
    print(json.dumps(dict(status='STARTED', **header)), flush=True)
    with Cadical195(bootstrap_with=f, with_proof=True) as solver:
        solver.conf_budget(budget)
        answer = solver.solve_limited()
        status = 'UNKNOWN'
        if answer:
            path = read_path(solver.get_model(), 9, 221, end)
            out.with_suffix('.path').write_text(' '.join(map(str, path))+'\n')
            status = 'SAT_PATH_VERIFIED'
        elif answer is False:
            cnf = out.with_suffix('.cnf')
            proof = out.with_suffix('.drat')
            f.to_file(str(cnf))
            proof.write_text('\n'.join(solver.get_proof())+'\n')
            with out.with_suffix('.check.log').open('w') as output:
                checked = subprocess.run([checker, str(cnf), str(proof)], stdout=output,
                                         stderr=subprocess.STDOUT)
            replay_log = out.with_suffix('.check.log').read_text()
            status = ('UNSAT_DRAT_VERIFIED' if checked.returncode == 0 and
                      's VERIFIED' in replay_log else 'UNSAT_REPLAY_FAILED')
        print(json.dumps(dict(status=status, **header, stats=solver.accum_stats())), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--control', action='store_true')
    parser.add_argument('--tight-pair', action='store_true')
    parser.add_argument('--distance', type=int, choices=(3,5,7,9))
    parser.add_argument('--budget', type=int, default=400000)
    parser.add_argument('--checker')
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    if args.control:
        control()
    else:
        search(args.distance, args.budget, args.checker, args.out, args.tight_pair)
