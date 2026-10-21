"""Round 2 drivers (Model2 from lns2.py, CaDiCaL, longer caps).

unknown : re-run the round-1 UNKNOWN windows of sweep80 with the strong model.
ends    : release both ends of every bank snake at once ([0,a) and [n-b,n)),
          optionally with a middle window; both endpoints may move far.
holes   : for bank snakes that leave vertices undominated, release every path
          position within Hamming distance r of an undominated vertex.
face    : release every path position inside a coordinate subcube.
grow    : LNS from a given start snake (e.g. the milestone 19 off-bank seed):
          uphill moves when possible, otherwise a different equal-length
          filling (neutral), regions chosen at random among windows, two
          windows, both ends and Hamming balls.
Every SAT answer is checked by lns.is_snake before it is logged.
"""
import argparse
import gzip
import itertools
import json
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lns import NB, NV, N, is_snake  # noqa: E402
from lns2 import Model2  # noqa: E402
from drive import canon, record, found  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
BANK = os.path.join(HERE, "../../../work/bank9.json")
SWEEP = os.path.join(HERE, "../data/sweep80.jsonl.gz")


def solve(P, R, target, tl, extra=None, **opt):
    kept = [v for i, v in enumerate(P) if i not in R]
    t = time.time()
    M = Model2(kept, target, **opt)
    if extra and M.ok:
        for c in extra(M):
            M.add(c)
    r, p = M.run(time_budget=tl)
    info = dict(free=len(M.free), cuts=M.cuts, vars=M.nvars, cls=M.nclauses,
                sec=round(time.time() - t, 2))
    M.close()
    if r == "SAT":
        assert is_snake(p) and len(p) >= target
    return r, p, info


def undominated(P):
    S = set(P)
    return [v for v in range(NV) if v not in S and not any(w in S for w in NB[v])]


def m_unknown(args, fh):
    bank = json.load(open(BANK))
    rows = [json.loads(l) for l in gzip.open(SWEEP, "rt")]
    rows = [r for r in rows if r["res"] == "UNKNOWN"]
    for r in rows:
        P = bank[r["bank"]]["vertex_sequence"]
        R = set(range(r["a"], r["a"] + r["w"]))
        res, p, info = solve(P, R, 193, args.tl)
        record(fh, dict(mode="unknown", bank=r["bank"], a=r["a"], w=r["w"], res=res, **info))
        print(r["bank"], r["a"], res, info, flush=True)
        if res == "SAT":
            found(p, fh, args.outdir)
            return


def m_ends(args, fh):
    bank = json.load(open(BANK))
    for bi in range(args.start, min(args.stop, len(bank))):
        P = bank[bi]["vertex_sequence"]
        n = len(P)
        for a, b in args.pairs:
            R = set(range(a)) | set(range(n - b, n))
            res, p, info = solve(P, R, 193, args.tl)
            record(fh, dict(mode="ends", bank=bi, a=a, b=b, res=res, **info))
            print(bi, a, b, res, info, flush=True)
            if res == "SAT":
                found(p, fh, args.outdir)
                return


def m_endsadapt(args, fh):
    """For each bank snake and split fraction f, release [0,a) and [n-b,n)
    with a + b = T, a = round(f T), increasing T from --t0 in steps of
    --tstep until the first UNKNOWN (larger releases contain smaller ones)."""
    bank = json.load(open(BANK))
    for bi in range(args.start, min(args.stop, len(bank))):
        P = bank[bi]["vertex_sequence"]
        n = len(P)
        for f in args.fracs:
            T = args.t0
            while T <= n:
                a = round(f * T)
                b = T - a
                R = set(range(a)) | set(range(n - b, n))
                res, p, info = solve(P, R, 193, args.tl)
                record(fh, dict(mode="endsadapt", bank=bi, f=f, a=a, b=b, res=res, **info))
                print(bi, f, a, b, res, info, flush=True)
                if res == "SAT":
                    found(p, fh, args.outdir)
                    return
                if res == "UNKNOWN":
                    break
                T += args.tstep


def m_holes(args, fh):
    bank = json.load(open(BANK))
    for bi in range(len(bank)):
        P = bank[bi]["vertex_sequence"]
        U = undominated(P)
        if not U:
            continue
        for rad in args.radii:
            R = set(i for i, v in enumerate(P) if min(bin(v ^ u).count("1") for u in U) <= rad)
            res, p, info = solve(P, R, 193, args.tl)
            record(fh, dict(mode="holes", bank=bi, holes=len(U), rad=rad, nrel=len(R), res=res, **info))
            print(bi, len(U), rad, len(R), res, info, flush=True)
            if res == "SAT":
                found(p, fh, args.outdir)
                return


def random_region(P, rng, wmin, wmax):
    n = len(P)
    kind = rng.random()
    if kind < 0.3:
        w = rng.randint(wmin, wmax)
        a = rng.randint(-w // 3, n - w + w // 3)
        return "win", set(i for i in range(a, a + w) if 0 <= i < n)
    if kind < 0.55:
        w1, w2 = rng.randint(wmin // 2, wmax // 2), rng.randint(wmin // 2, wmax // 2)
        a1, a2 = rng.randint(0, n - w1), rng.randint(0, n - w2)
        return "two", set(range(a1, a1 + w1)) | set(range(a2, a2 + w2))
    if kind < 0.75:
        a, b = rng.randint(wmin // 3, wmax // 2), rng.randint(wmin // 3, wmax // 2)
        return "ends", set(range(a)) | set(range(n - b, n))
    c = rng.randrange(NV)
    rad = rng.choice([3, 4, 4])
    R = sorted((i for i, v in enumerate(P) if bin(v ^ c).count("1") <= rad),
               key=lambda i: bin(P[i] ^ c).count("1"))
    return f"ball{rad}", set(R[: wmax + 20])


def m_grow(args, fh):
    rng = random.Random(args.seed)
    if args.start_file:
        d = json.load(open(args.start_file))
        P = d.get("vertex_sequence") or d.get("path_vertices")
    else:
        P = json.load(open(BANK))[args.start]["vertex_sequence"]
    assert is_snake(P)
    bankc = {canon(r["vertex_sequence"]): i for i, r in enumerate(json.load(open(BANK)))}
    t_end = time.time() + args.hours * 3600
    step = 0
    best = len(P)
    while time.time() < t_end:
        step += 1
        kind, R = random_region(P, rng, args.wmin, args.wmax)
        if len(R) < 5:
            continue
        L = len(P)
        tgt = L + 1
        r, p, info = solve(P, R, tgt, args.tl)
        rec = dict(mode="grow", step=step, kind=kind, nrel=len(R), L=L - 1, up=r, **info)
        if r == "SAT":
            P = p
            rec["moved"] = "up"
        else:
            old = [P[i] for i in R]

            def differ(M, old=old):
                lits = [-M.x[v] for v in old if v in M.x]
                return [lits] if lits else []

            r2, p2, info2 = solve(P, R, L, args.tl / 2, extra=differ)
            rec.update(side=r2, sec2=info2["sec"])
            if r2 == "SAT":
                P = p2
                rec["moved"] = "flat"
        rec["len"] = len(P) - 1
        if len(P) == 192:
            rec["bank"] = bankc.get(canon(P), -1)
        record(fh, rec)
        print(step, kind, len(R), rec["len"], r, rec.get("side"), info["free"], info["sec"], flush=True)
        if len(P) >= 193:
            found(P, fh, args.outdir)
            return
        if len(P) > best or step % 20 == 0:
            best = max(best, len(P))
            with open(os.path.join(args.outdir, f"grow-state-{args.seed}.json"), "w") as f:
                json.dump({"step": step, "edges": len(P) - 1, "vertex_sequence": P}, f)


def m_faceall(args, fh):
    """Every coordinate subcube of dimension --dim of every bank snake."""
    bank = json.load(open(BANK))
    for bi in (args.banks or range(args.start, min(args.stop, len(bank)))):
        P = bank[bi]["vertex_sequence"]
        for dims in itertools.combinations(range(N), args.dim):
            mask = sum(1 << d for d in dims)
            for base in range(NV):
                if base & mask:
                    continue
                R = set(i for i, v in enumerate(P) if v & ~mask == base)
                res, p, info = solve(P, R, 193, args.tl)
                record(fh, dict(mode="faceall", bank=bi, dims=list(dims), base=base, nrel=len(R), res=res, **info))
                if res != "UNSAT":
                    print(bi, dims, base, len(R), res, info, flush=True)
                if res == "SAT":
                    found(p, fh, args.outdir)
                    return
        print("done", bi, flush=True)


def m_face(args, fh):
    bank = json.load(open(BANK))
    rng = random.Random(args.seed)
    t_end = time.time() + args.hours * 3600
    while time.time() < t_end:
        bi = rng.choice(args.banks) if args.banks else rng.randrange(len(bank))
        P = bank[bi]["vertex_sequence"]
        dims = rng.sample(range(N), args.dim)
        mask = sum(1 << d for d in dims)
        base = rng.randrange(NV) & ~mask
        R = set(i for i, v in enumerate(P) if v & ~mask == base)
        res, p, info = solve(P, R, 193, args.tl)
        record(fh, dict(mode="face", bank=bi, dims=sorted(dims), base=base, nrel=len(R), res=res, **info))
        print(bi, sorted(dims), base, len(R), res, info, flush=True)
        if res == "SAT":
            found(p, fh, args.outdir)
            return


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["unknown", "ends", "endsadapt", "holes", "grow", "face", "faceall"])
    ap.add_argument("--log", required=True)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--tl", type=float, default=60)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--stop", type=int, default=10 ** 9)
    ap.add_argument("--pairs", type=lambda s: [tuple(map(int, p.split(":"))) for p in s.split(",")],
                    default=[(45, 45)])
    ap.add_argument("--fracs", type=float, nargs="+", default=[0.25, 0.5, 0.75])
    ap.add_argument("--t0", type=int, default=100)
    ap.add_argument("--tstep", type=int, default=10)
    ap.add_argument("--radii", type=int, nargs="+", default=[2, 3])
    ap.add_argument("--start-file")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--hours", type=float, default=1)
    ap.add_argument("--wmin", type=int, default=40)
    ap.add_argument("--wmax", type=int, default=100)
    ap.add_argument("--dim", type=int, default=6)
    ap.add_argument("--banks", type=int, nargs="*")
    args = ap.parse_args()
    os.makedirs(args.outdir, exist_ok=True)
    with open(args.log, "a") as fh:
        globals()["m_" + args.mode](args, fh)


if __name__ == "__main__":
    main()
