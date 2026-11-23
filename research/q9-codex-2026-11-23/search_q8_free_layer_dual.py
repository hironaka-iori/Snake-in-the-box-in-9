"""Generate integer upper certificates for a free Q8 partner arm by face LP.

Use --input for a JSONL of first-layer vertex sequences. Solver floating-point
numbers merely suggest weights. verify_q8_free_layer_dual.py checks the saved
bounds with exact integers independently of SciPy and HiGHS.
"""

import time, json, random
from itertools import combinations
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import vstack, csr_matrix
from scipy.sparse import coo_matrix
from functools import lru_cache


@lru_cache(None)
def local(size, mask):
    nb = [[v ^ (1 << k) for k in range(size)] for v in range(1 << size)]
    p = mask
    result = []
    while True:
        live = [i for i in range(1 << size) if p >> i & 1]
        states = {
            v: sum(1 << k for k, w in enumerate(nb[v]) if p >> w & 1) for v in live
        }
        if all(z.bit_count() <= 2 for z in states.values()):
            seen = set()
            bad = False
            for v in live:
                if v in seen:
                    continue
                stack = [v]
                seen.add(v)
                deg = verts = 0
                while stack:
                    w = stack.pop()
                    verts += 1
                    deg += states[w].bit_count()
                    for k, z in enumerate(nb[w]):
                        if states[w] >> k & 1 and z not in seen:
                            seen.add(z)
                            stack.append(z)
                if deg >= 2 * verts:
                    bad = True
                    break
            if not bad:
                result.append(states)
        if not p:
            break
        p = (p - 1) & mask
    return result


def solve(arm, axislist, ep):
    root = arm[0]
    A = set(range(256)) - set(arm[1:])
    cols = []
    rhs = []
    names = {}
    groups = []
    obj = []

    def row(name, b=0):
        if name not in names:
            names[name] = len(rhs)
            rhs.append(b)
        return names[name]

    master = {}
    endrow = row(("end",), 1)
    for v in sorted(A):
        group = []
        links = master[v] = {}
        nb = [k for k in range(8) if (v ^ (1 << k)) in A]
        opts = [tuple()] if v != root else []
        if v == root or (v ^ root).bit_count() % 2 == ep:
            opts += list(combinations(nb, 1))
        if v != root:
            opts += list(combinations(nb, 2))
        for axes in opts:
            z = sum(1 << k for k in axes)
            data = {row(("v", v), 1): 1}
            if len(axes) == 1 and v != root:
                data[endrow] = 1
            idx = len(cols)
            cols.append(data)
            obj.append(int(bool(axes)))
            group.append(idx)
            links[z] = idx
        groups.append(group)
    for axes in axislist:
        k = len(axes)
        tot = sum(1 << d for d in axes)
        delta = [
            sum(1 << d for i, d in enumerate(axes) if s >> i & 1) for s in range(1 << k)
        ]
        for t in range(256):
            if t & tot:
                continue
            face = [t ^ d for d in delta]
            mask = sum(1 << i for i, v in enumerate(face) if v in A)
            if not mask:
                continue
            p = local(k, mask)
            tile = row(("tile", tot, t), 1)
            group = []
            local_rows = {}
            for j, v in enumerate(face):
                if v not in A:
                    continue
                for z, idx in master[v].items():
                    if not z:
                        continue
                    a = sum(1 << i for i, d in enumerate(axes) if z >> d & 1)
                    r = row((tot, v, a))
                    cols[idx][r] = -1
                    local_rows[j, a] = r
            for states in p:
                if any((j, a) not in local_rows for j, a in states.items()):
                    continue
                if root in face and face.index(root) not in states:
                    continue
                data = {tile: 1}
                for j, a in states.items():
                    data[local_rows[j, a]] = 1
                idx = len(cols)
                cols.append(data)
                obj.append(0)
                group.append(idx)
            groups.append(group)
    I = []
    J = []
    V = []
    for j, col in enumerate(cols):
        for i, v in col.items():
            I.append(i)
            J.append(j)
            V.append(v)
    mat = coo_matrix(
        (np.array(V, dtype=np.int64), (I, J)), shape=(len(rhs), len(cols))
    ).tocsc()
    rhs = np.array(rhs, dtype=np.int64)
    c = np.array(obj, dtype=np.int64)
    # Alternation pins the two parity population counts up to the prescribed
    # endpoint colour. A hypothetical longer/shorter path of the SAME parity
    # satisfies the same equation.
    paritycol = np.array([0] * len(cols), dtype=np.int64)
    for w, links in master.items():
        for z, j in links.items():
            if z:
                paritycol[j] = 1 if ((w ^ root).bit_count() % 2 == 0) else -1
    mat = vstack([mat, csr_matrix(paritycol.reshape(1, -1))], format="csc")
    rhs = np.append(rhs, int(ep == 0))
    t = time.monotonic()
    lp = linprog(
        -c,
        A_eq=mat,
        b_eq=rhs,
        bounds=(0, None),
        method="highs",
        options={"time_limit": 90.0, "threads": 1},
    )
    output = {
        "status": lp.message,
        "rows": len(rhs),
        "vars": len(cols),
        "seconds": round(time.monotonic() - t, 2),
    }
    if lp.success:
        scale = 100000
        y = np.rint(-lp.eqlin.marginals * scale).astype(np.int64)
        residual = c * scale - mat.T @ y
        unitbound = int(rhs @ y) + sum(int(max(residual[g])) for g in groups)
        output.update(
            numerical=-lp.fun,
            integer_numerator=unitbound,
            scale=scale,
            vertices_upper=unitbound // scale,
        )
        nonzero = [
            [key[0], key[1], key[2], int(y[j])]
            for key, j in names.items()
            if isinstance(key[0], int) and y[j]
        ]
        output["certificate"] = {
            "arm": arm,
            "end_parity": ep,
            "scale": scale,
            "directions": axislist,
            "end_weight": int(y[endrow]),
            "parity_weight": int(y[-1]),
            "matching_weights": nonzero,
            "integer_numerator": unitbound,
        }

    return output


if __name__ == "__main__":
    import argparse

    pa = argparse.ArgumentParser()
    pa.add_argument("--parts", type=int, default=12)
    pa.add_argument("--k", type=int, default=3)
    pa.add_argument("--min-edges", type=int, default=96)
    pa.add_argument("--max-edges", type=int, default=98)
    pa.add_argument("--total-edges", type=int, default=192)
    pa.add_argument("--bank", action="store_true")
    pa.add_argument("--limit", type=int, default=100)
    pa.add_argument("--offset", type=int, default=0)
    pa.add_argument("--input", type=Path)
    args = pa.parse_args()
    if args.input:
        arms = [json.loads(l) for l in args.input.read_text().splitlines()]
    elif args.bank:
        arms = []
        for s in sorted(
            Path("/private/tmp/q8_via_seven_20261119.txt").read_text().splitlines(),
            key=lambda s: -len(s),
        ):
            p = [0]
            for d in s:
                p.append(p[-1] ^ (1 << int(d)))
            arms.append(p)
    else:
        ref = json.loads(
            next(
                Path("/Users/yichenzhan/Documents/Codex/2026-11-02").glob(
                    "*/Snake*/outputs/snake8_witness.json"
                )
            ).read_text()
        )["vertex_sequence"]
        arms = []
        for length in range(args.max_edges, args.min_edges - 1, -1):
            for i in range(len(ref) - length):
                p = ref[i : i + length + 1]
                arms.extend([p, p[::-1]])
    sets = list(combinations(range(8), args.k))
    random.Random(314).shuffle(sets)
    axes = sets[: args.parts]
    for idx, arm in enumerate(
        arms[args.offset : args.offset + args.limit], args.offset
    ):
        ep = (args.total_edges - len(arm)) % 2
        ans = solve(arm, axes, ep)
        print(
            json.dumps(
                dict(
                    index=idx,
                    lower_edges=len(arm) - 1,
                    total_edges=args.total_edges,
                    target_vertices=args.total_edges + 1 - len(arm),
                    **ans,
                ),
                separators=(",", ":"),
            ),
            flush=True,
        )
