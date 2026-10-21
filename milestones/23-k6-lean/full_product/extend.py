"""Cheaper replacements for expensive keys: plain-test their one-step extensions.

For every key of KEYS.json whose estimated cost (prune.load_costs) exceeds MIN hints, every
window that extends it by one direction and one count on the left or on the right (induced,
at most 6 counts) is UNSAT too; such a window is often much easier for the solver.  Each
untested extension is plain-tested (radius 4, k6loop oracle; logged in oracle_full.jsonl with
its solve time), so that prune.py can choose it instead of the expensive key.

usage: nice -n 19 python extend.py KEYS.json MIN_HINTS [TL] [--reuse]
"""
import sys, os, json, time
sys.dont_write_bytecode = True
import fp, prune as PR
from fp import GA


def extensions(k):
    ds, t = k; out = set()
    if len(t) >= 6:
        return out
    m = max(ds)
    for d in range(min(m + 2, 9)):
        for s in range(1, 7):
            for nds, nt in (((d,) + tuple(ds), (s,) + tuple(t)), (tuple(ds) + (d,), tuple(t) + (s,))):
                if GA.induced(nds):
                    out.add(fp.lkey(nds, nt))
    return out


def main():
    ks = [PR.lumped_of(d, a) for d, a in json.load(open(sys.argv[1]))['keys']]
    mn = float(sys.argv[2]); tl = float(sys.argv[3]) if len(sys.argv) > 3 and not sys.argv[3].startswith('-') else 60
    cost, how, cert = PR.load_costs(ks, '--reuse' in sys.argv)
    S = fp.Status()
    big = sorted([i for i in range(len(ks)) if cost[i] > mn], key=lambda i: -cost[i])
    print(f'{len(big)} keys above {mn:.0f} hints', flush=True)
    t0 = time.time()
    for i in big:
        ext = sorted(e for e in extensions(ks[i]) if S.st.get(e) is None)
        res = {}
        for e in ext:
            r = S.test(e, tl)
            res[r['result']] = res.get(r['result'], 0) + 1
        print(json.dumps(dict(key=[list(ks[i][0]), list(ks[i][1])], cost_M=round(cost[i] / 1e6, 1),
                              tested=len(ext), results=res, t=round(time.time() - t0))), flush=True)


if __name__ == '__main__':
    main()
