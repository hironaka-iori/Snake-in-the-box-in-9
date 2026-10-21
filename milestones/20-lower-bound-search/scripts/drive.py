"""Drivers for the large-neighbourhood search.

sweep : every bank snake, contiguous released windows, target 193 vertices.
walk  : plateau random walk.  From a current 191-edge snake, release a random
        region; first ask for 193 selected vertices (a 192-edge snake); if that
        is refuted, ask for a *different* 192-vertex filling and move to it.
Every SAT answer is re-checked with lns.is_snake before it is logged.
"""
import argparse
import json
import random
import sys
import time
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lns import Model, is_snake, NB  # noqa: E402

BANK = os.path.join(os.path.dirname(__file__), "../../../work/bank9.json")


def canon(seq):
    """Canonical transition sequence up to translation, coordinate permutation, reversal."""
    best = None
    for s in (seq, seq[::-1]):
        trans = [(s[i] ^ s[i + 1]).bit_length() - 1 for i in range(len(s) - 1)]
        mp = {}
        out = []
        for t in trans:
            if t not in mp:
                mp[t] = len(mp)
            out.append(mp[t])
        out = tuple(out)
        if best is None or out < best:
            best = out
    return best


def record(fh, obj):
    fh.write(json.dumps(obj) + "\n")
    fh.flush()


def found(path, fh, outdir):
    assert is_snake(path)
    edges = len(path) - 1
    record(fh, {"FOUND": edges, "path": path})
    with open(os.path.join(outdir, f"snake{edges}-{int(time.time())}.json"), "w") as f:
        json.dump({"edges": edges, "vertex_sequence": path}, f)
    print("FOUND", edges, flush=True)


def solve(P, R, target, tl, extra=None):
    kept = [v for i, v in enumerate(P) if i not in R]
    M = Model(kept, target)
    if extra and M.ok:
        for c in extra(M):
            M.s.add_clause(c)
    t = time.time()
    r, p = M.run(time_budget=tl)
    info = dict(free=len(M.free), cuts=M.cuts, sec=round(time.time() - t, 2))
    M.close()
    return r, p, info


def sweep(args, fh):
    bank = json.load(open(BANK))
    for bi in range(args.start, len(bank)):
        P = bank[bi]["vertex_sequence"]
        for w in args.widths:
            for a in range(0, len(P) - w + 1, args.step):
                if args.wrap_ends and a + w > len(P):
                    continue
                R = set(range(a, a + w))
                r, p, info = solve(P, R, 193, args.tl)
                record(fh, dict(mode="sweep", bank=bi, a=a, w=w, res=r, **info))
                if r == "SAT":
                    found(p, fh, args.outdir)
                    return


def random_region(P, rng, wmin, wmax):
    kind = rng.random()
    n = len(P)
    if kind < 0.4:
        w = rng.randint(wmin, wmax)
        a = rng.randint(-w // 3, n - w + w // 3)
        return "win", set(i for i in range(a, a + w) if 0 <= i < n)
    if kind < 0.75:
        w1 = rng.randint(wmin // 2, wmax // 2)
        w2 = rng.randint(wmin // 2, wmax // 2)
        a1 = rng.randint(0, n - w1)
        a2 = rng.randint(0, n - w2)
        return "two", set(range(a1, a1 + w1)) | set(range(a2, a2 + w2))
    # Hamming ball around a random vertex of the cube
    c = rng.randrange(512)
    rad = rng.choice([3, 3, 4])
    R = set(i for i, v in enumerate(P) if bin(v ^ c).count("1") <= rad)
    if len(R) > wmax + 20:
        R = set(sorted(R, key=lambda i: bin(P[i] ^ c).count("1"))[: wmax + 20])
    return f"ball{rad}", R


def walk(args, fh):
    bank = json.load(open(BANK))
    rng = random.Random(args.seed)
    seen = set(canon(r["vertex_sequence"]) for r in bank)
    nbank = len(seen)
    P = bank[args.start % len(bank)]["vertex_sequence"]
    t_end = time.time() + args.hours * 3600
    step = 0
    while time.time() < t_end:
        step += 1
        kind, R = random_region(P, rng, args.wmin, args.wmax)
        if len(R) < 5:
            continue
        r, p, info = solve(P, R, 193, args.tl)
        rec = dict(mode="walk", step=step, kind=kind, nrel=len(R), res193=r, **info)
        if r == "SAT":
            record(fh, rec)
            found(p, fh, args.outdir)
            return
        # neutral move: a different 192-vertex filling of the same region
        old = [P[i] for i in R]

        def differ(M):
            lits = [-M.x[v] for v in old if v in M.x]
            return [lits] if lits else []

        r2, p2, info2 = solve(P, R, 192, args.tl, extra=differ)
        rec.update(res192=r2, sec192=info2["sec"])
        if r2 == "SAT" and is_snake(p2) and len(p2) == 192:
            P = p2
            c = canon(P)
            rec["new_class"] = c not in seen
            seen.add(c)
        rec["classes"] = len(seen) - nbank
        record(fh, rec)
        if step % 50 == 0:
            with open(os.path.join(args.outdir, f"walk-state-{args.seed}.json"), "w") as f:
                json.dump({"step": step, "vertex_sequence": P, "new_classes": len(seen) - nbank}, f)


def anneal(args, fh):
    """LNS with length moves.  State: a snake P (len(P) vertices).  Each step
    releases a random region and asks for len(P)+1 vertices (uphill).  If that
    is refuted, it moves to a different filling with len(P) vertices
    (neutral) or, with probability --pdown and while len(P) > --floor,
    len(P)-1 vertices (downhill)."""
    bank = json.load(open(BANK))
    rng = random.Random(args.seed)
    bankc = {canon(r["vertex_sequence"]): i for i, r in enumerate(bank)}
    seen = set()
    P = bank[args.start % len(bank)]["vertex_sequence"]
    t_end = time.time() + args.hours * 3600
    step = 0
    best = len(P)
    while time.time() < t_end:
        step += 1
        kind, R = random_region(P, rng, args.wmin, args.wmax)
        if len(R) < 5:
            continue
        L = len(P)
        r, p, info = solve(P, R, L + 1, args.tl)
        rec = dict(mode="anneal", step=step, kind=kind, nrel=len(R), L=L - 1, up=r, **info)
        if r == "SAT":
            assert is_snake(p) and len(p) >= L + 1
            P = p
            rec["moved"] = "up"
        else:
            old = [P[i] for i in R]

            def differ(M):
                lits = [-M.x[v] for v in old if v in M.x]
                return [lits] if lits else []

            tgt = L - 1 if (L - 1 > args.floor and rng.random() < args.pdown) else L
            r2, p2, info2 = solve(P, R, tgt, args.tl, extra=differ)
            rec.update(side=r2, tgt=tgt - 1, sec2=info2["sec"])
            if r2 == "SAT":
                assert is_snake(p2)
                P = p2
                rec["moved"] = "down" if len(P) < L else "flat"
        if len(P) >= 193:
            record(fh, rec)
            found(P, fh, args.outdir)
            return
        c = canon(P)
        rec["len"] = len(P) - 1
        if len(P) == 192:
            rec["bank"] = bankc.get(c, -1)
        seen.add(c)
        rec["distinct"] = len(seen)
        record(fh, rec)
        if len(P) > best or step % 50 == 0:
            best = max(best, len(P))
            with open(os.path.join(args.outdir, f"anneal-state-{args.seed}.json"), "w") as f:
                json.dump({"step": step, "vertex_sequence": P}, f)


def ils(args, fh):
    """Iterated local search.  Kick: --kick downhill moves, each replacing a
    random region by a *different* filling with exactly one vertex fewer.
    Climb: up to --climb steps of uphill (len+1) or neutral moves; stop after
    --patience consecutive steps without an uphill move.  The climb restarts
    from the best snake of the episode if it ends below 191 edges."""
    from pysat.card import CardEnc, EncType
    bank = json.load(open(BANK))
    rng = random.Random(args.seed)
    bankc = {canon(r["vertex_sequence"]): i for i, r in enumerate(bank)}
    home = bank[args.start % len(bank)]["vertex_sequence"]
    P = home
    t_end = time.time() + args.hours * 3600
    ep = 0
    new191 = {}
    while time.time() < t_end:
        ep += 1
        # kick
        kicks = 0
        tries = 0
        while kicks < args.kick and tries < 4 * args.kick:
            tries += 1
            kind, R = random_region(P, rng, args.wmin, args.wmax)
            if len(R) < 5:
                continue
            old = [P[i] for i in R]
            L = len(P)

            def down(M, old=old, L=L):
                lits = [-M.x[v] for v in old if v in M.x]
                cl = [lits] if lits else []
                enc = CardEnc.atmost(list(M.x.values()), bound=L - 1 - len(M.kept),
                                     top_id=M.top, encoding=EncType.seqcounter)
                return cl + enc.clauses

            r, p, info = solve(P, R, L - 1, args.tl, extra=down)
            if r == "SAT":
                assert is_snake(p) and len(p) == L - 1
                P = p
                kicks += 1
        low = len(P) - 1
        # climb
        ups = 0
        idle = 0
        for st in range(args.climb):
            if idle >= args.patience or time.time() > t_end:
                break
            kind, R = random_region(P, rng, args.wmin, args.wmax)
            if len(R) < 5:
                continue
            L = len(P)
            r, p, info = solve(P, R, L + 1, args.tl)
            if r == "SAT":
                assert is_snake(p) and len(p) > L
                P = p
                ups += 1
                idle = 0
                if len(P) >= 193:
                    found(P, fh, args.outdir)
                    return
                continue
            idle += 1
            old = [P[i] for i in R]

            def differ(M, old=old):
                lits = [-M.x[v] for v in old if v in M.x]
                return [lits] if lits else []

            r2, p2, _ = solve(P, R, L, args.tl, extra=differ)
            if r2 == "SAT":
                assert is_snake(p2)
                P = p2
        top = len(P) - 1
        rec = dict(mode="ils", episode=ep, low=low, top=top, ups=ups)
        if top == 191:
            c = canon(P)
            rec["bank"] = bankc.get(c, -1)
            if c not in bankc:
                new191[c] = P
                with open(os.path.join(args.outdir, f"new191-{args.seed}-{len(new191)}.json"), "w") as f:
                    json.dump({"edges": 191, "vertex_sequence": P}, f)
            rec["new191"] = len(new191)
        else:
            rec["path"] = P
        record(fh, rec)
        if top < args.reset:
            P = home


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["sweep", "walk", "anneal", "ils"])
    ap.add_argument("--log", required=True)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--widths", type=int, nargs="+", default=[64])
    ap.add_argument("--step", type=int, default=8)
    ap.add_argument("--tl", type=float, default=20)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--hours", type=float, default=1)
    ap.add_argument("--wmin", type=int, default=40)
    ap.add_argument("--wmax", type=int, default=90)
    ap.add_argument("--wrap-ends", action="store_true")
    ap.add_argument("--pdown", type=float, default=0.3)
    ap.add_argument("--kick", type=int, default=4)
    ap.add_argument("--climb", type=int, default=200)
    ap.add_argument("--patience", type=int, default=40)
    ap.add_argument("--reset", type=int, default=189)
    ap.add_argument("--floor", type=int, default=188)
    args = ap.parse_args()
    with open(args.log, "a") as fh:
        {"sweep": sweep, "walk": walk, "anneal": anneal, "ils": ils}[args.mode](args, fh)


if __name__ == "__main__":
    main()
