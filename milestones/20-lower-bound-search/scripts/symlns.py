"""Round 3: large-neighbourhood search inside the space of g-symmetric snakes.

A symmetric snake p (g(p[i]) = p[len-1-i], class (k, w), normalised as in
sym3.SymModel) is repaired by releasing a set R of half positions
r(i) = min(i, len-1-i).  Orbits of the kept positions are passed to a
persistent SymModel as assumptions, so learned clauses and cycle cuts are
shared between steps.  Because every orbit has two vertices, a release of
W half positions frees about twice as many cube vertices as a W-position
window of rounds 1-2.

Step: ask for len+2 vertices (one more orbit); if refuted, ask for a
different filling of the same length (neutral move, enforced by a selector
clause "some released old orbit is dropped").  Every accepted state is
checked by sym3.is_snake and for g-invariance.
"""
import argparse
import json
import os
import random
import resource
import shutil
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sym3 import SymModel, is_snake  # noqa: E402


class SymLNS:
    def __init__(self, n, k, w, tl, seed, log, outdir, wmin, wmax, best_save=0):
        self.n, self.k, self.w, self.tl = n, k, w, tl
        self.rng = random.Random(seed)
        self.models = {}
        self.log, self.outdir = log, outdir
        self.wmin, self.wmax = wmin, wmax
        self.best = best_save
        self.W = wmin
        self.patience = 40

    def model(self, nverts):
        for key in list(self.models):
            if abs(key - nverts) > 2:
                self.models.pop(key).close()
        if nverts not in self.models:
            self.models[nverts] = SymModel(self.n, self.k, self.w, nverts)
        return self.models[nverts]

    def region(self, p):
        nv = len(p)
        H = (nv - 1) // 2
        r = lambda i: min(i, nv - 1 - i)  # noqa: E731
        kind = self.rng.choice(["win", "win", "two", "ends", "ball"])
        W = max(4, min(H + 1, self.W + self.rng.randint(-3, 3)))
        if kind == "win":
            a = self.rng.randint(0, max(0, H + 1 - W))
            R = set(range(a, a + W))
        elif kind == "ends":
            R = set(range(0, W))
        elif kind == "two":
            R = set()
            for _ in range(2):
                a = self.rng.randint(0, max(0, H + 1 - W // 2))
                R |= set(range(a, a + W // 2))
        else:
            c = p[self.rng.randrange(nv)]
            rad = 4 if self.W >= 40 else 3
            R = {r(i) for i in range(nv) if bin(p[i] ^ c).count("1") <= rad}
        return kind, R

    def attempt(self, p, R, nverts, different):
        M = self.model(nverts)
        nv = len(p)
        keep = {M.orb[p[i]] for i in range(nv) if min(i, nv - 1 - i) not in R}
        rel = {M.orb[p[i]] for i in range(nv)} - keep
        ass = sorted(keep)
        if different:
            sel = M.new()
            M.s.add_clause([-sel] + [-o for o in sorted(rel)])
            ass.append(sel)
        st, q = M.run(self.tl, assumptions=ass)
        return st, q, len(rel)

    def save(self, q, tag):
        fn = os.path.join(self.outdir, f"symlns-k{self.k}-e{len(q) - 1}-{tag}.json")
        json.dump({"vertex_sequence": q, "class": [self.k, self.w]}, open(fn, "w"))
        return fn

    def walk(self, p, hours, logf):
        t_end = time.time() + 3600 * hours
        step = 0
        stale = 0
        while time.time() < t_end:
            if shutil.disk_usage("/").free < 300 * 2**20:
                print("low disk", flush=True)
                break
            step += 1
            kind, R = self.region(p)
            t0 = time.time()
            st, q, nrel = self.attempt(p, R, len(p) + 2, False)
            move = "up"
            if st != "SAT" and stale >= self.patience and len(p) > 3:
                st2, q2, _ = self.attempt(p, R, len(p) - 2, True)
                move, st, q = "kick", st + "/" + st2, q2
                if q is not None:
                    stale = 0
            elif st != "SAT":
                st2, q2, _ = self.attempt(p, R, len(p), True)
                move, st, q = "neutral", st + "/" + st2, q2
            stale = 0 if move == "up" and q is not None else stale + 1
            up_st = st.split("/")[0]
            if up_st == "UNKNOWN":
                self.W = max(self.wmin, self.W - 3)
            elif up_st == "UNSAT":
                self.W = min(self.wmax, self.W + 2)
            rec = dict(step=step, k=self.k, w=self.w, len=len(p) - 1, kind=kind, released=len(R),
                       rel_orbits=nrel, move=move, status=st, t=round(time.time() - t0, 1),
                       W=self.W, rss_mb=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024)
            if q is not None:
                g = self.models[len(q)].g
                assert is_snake(q, self.n) and sorted(map(g, q)) == sorted(q)
                p = q
                rec["new_len"] = len(p) - 1
                if len(p) - 1 > self.best:
                    self.best = len(p) - 1
                    rec["file"] = self.save(p, f"s{step}")
            print(json.dumps(rec), flush=True)
            logf.write(json.dumps(rec) + "\n")
            logf.flush()
        return p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=9)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--start", required=True, help="JSON with vertex_sequence (symmetric, normalised)")
    ap.add_argument("--hours", type=float, default=1.0)
    ap.add_argument("--tl", type=float, default=30)
    ap.add_argument("--wmin", type=int, default=20)
    ap.add_argument("--wmax", type=int, default=50)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--patience", type=int, default=40)
    ap.add_argument("--log", required=True)
    ap.add_argument("--outdir", required=True)
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    p = json.load(open(a.start))["vertex_sequence"]
    w = 0 if len(p) % 2 else 1
    S = SymLNS(a.n, a.k, w, a.tl, a.seed, a.log, a.outdir, a.wmin, a.wmax, best_save=len(p) - 1)
    S.patience = a.patience
    with open(a.log, "a") as f:
        S.walk(p, a.hours, f)


if __name__ == "__main__":
    main()
