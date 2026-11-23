"""Search for an induced path with fixed length and endpoint-distance orbit."""
import argparse
import gzip
import itertools
import json
import subprocess
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195


def build(dim, length, distance, *, include_rank=True):
    assert 1 <= distance <= min(dim, length) and (length-distance) % 2 == 0
    n = 1 << dim
    end = (1 << distance) - 1
    height = (length - distance) // 2
    selected = [v + 1 for v in range(n)]
    pool = IDPool(start_from=n + 1)
    f = CNF()
    for parity in (0, 1):
        group = [selected[v] for v in range(n) if v.bit_count() % 2 == parity]
        count = (length + 2 - parity) // 2
        f.extend(CardEnc.equals(group, count, vpool=pool, encoding=EncType.totalizer).clauses)
    for v in range(n):
        neighbors = [selected[v ^ (1 << j)] for j in range(dim)]
        need = 1 if v in (0, end) else 2
        if need == 1:
            f.append([selected[v]])
        for extra in itertools.combinations(neighbors, need + 1):
            f.append([-selected[v], *(-x for x in extra)])
        for missing in itertools.combinations(neighbors, need - 1):
            f.append([-selected[v], *(x for x in neighbors if x not in missing)])

    if not include_rank:
        return f, end

    # q=(position - Hamming weight)/2. Threshold t is the predicate q >= t.
    levels = [[pool.id() for _ in range(height)] for v in range(n)]
    for v, row in enumerate(levels):
        for previous, following in zip(row, row[1:]):
            f.append([-following, previous])
        if v in (0, end):
            for bit in row:
                f.append([bit if v == end else -bit])
    for low in range(n):
        for j in range(dim):
            high = low | (1 << j)
            if high == low:
                continue
            guard = [-selected[low], -selected[high]]
            for t in range(height):
                # q(high) <= q(low) <= q(high)+1.
                f.append([*guard, -levels[high][t], levels[low][t]])
                if t:
                    f.append([*guard, -levels[low][t], levels[high][t-1]])
    return f, end


def read_path(model, dim, length, end):
    points = {x-1 for x in model if 1 <= x <= 1 << dim}
    assert len(points) == length + 1
    p = [0]
    while p[-1] != end:
        choices = (points - set(p)).intersection(p[-1] ^ (1 << i) for i in range(dim))
        assert len(choices) == 1
        p.append(choices.pop())
    assert len(p) == length + 1
    assert all(((a ^ b).bit_count() == 1) == (i == j + 1)
               for i, a in enumerate(p) for j, b in enumerate(p[:i]))
    return p


def run(dim, length, distance, budget, bank, proof_dir, prefix=None, pair17=False):
    f, end = build(dim, length, distance)
    if pair17:
        assert (dim, length) == (9, 221)
        from q9_free_pair_cuts import add_pair_cuts
        add_pair_cuts(f, f.nv, minimum=17)
    if prefix:
        v = 0
        for axis in prefix:
            assert 0 <= axis < dim
            v ^= 1 << axis
            f.append([v+1])
    if bank:
        with gzip.open(bank, "rt") as src:
            sample = next(list(map(int, line.split())) for line in src
                          if (int(line.split()[0]) ^ int(line.split()[-1])).bit_count() == distance)
        origin = sample[0]
        delta = origin ^ sample[-1]
        order = sorted(range(dim), key=lambda d: not (delta >> d & 1))
        points = {sum((((v ^ origin) >> d) & 1) << j for j, d in enumerate(order)) for v in sample}
        assert len(points) == length + 1
        for v in points:
            f.append([v+1])
    with Cadical195(bootstrap_with=f, with_proof=bool(proof_dir)) as sat:
        sat.conf_budget(budget)
        ans = sat.solve_limited()
        result = dict(dimension=dim, length=length, distance=distance, pinned=bool(bank), prefix=prefix, pair17=pair17,
                      variables=f.nv, clauses=len(f.clauses), conflicts=sat.accum_stats()["conflicts"])
        if ans:
            result.update(status="SAT_path_checked", path=read_path(sat.get_model(), dim, length, end))
        elif ans is False:
            result.update(status="UNSAT_solver")
            if proof_dir:
                folder, checker = proof_dir
                suffix = "_pair17" if pair17 else ""
                if prefix:
                    suffix += "_p" + "".join(map(str, prefix))
                stem = Path(folder) / f"q{dim}_l{length}_d{distance}{suffix}"
                f.to_file(str(stem)+".cnf")
                Path(str(stem)+".drat").write_text("\n".join(sat.get_proof())+"\n")
                check = subprocess.run([checker,str(stem)+".cnf",str(stem)+".drat"],
                                       capture_output=True,check=True)
                assert b"s VERIFIED" in check.stdout
                result["status"] = "UNSAT_DRAT_verified"
        else:
            result.update(status="UNKNOWN")
        print(json.dumps(result), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    for name in ["dimension","length","distance","budget"]:
        p.add_argument(name,type=int)
    p.add_argument("--bank")
    p.add_argument("--proof-dir",nargs=2,metavar=("DIRECTORY","DRAT_TRIM"))
    p.add_argument("--prefix",type=int,nargs="+")
    p.add_argument("--pair17",action="store_true")
    a=p.parse_args()
    run(a.dimension,a.length,a.distance,a.budget,a.bank,a.proof_dir,a.prefix,a.pair17)
