"""Check a sample of widened keys E(K) as statements of their own.

For a seed K whose E(K) is trimmed (shorter window) and covers other keys, build the radius-4 CNF
of E itself (wincert.Encoding(winOf E.ds, E.ranges, 4); an uncounted centre is None) and solve
it.  UNSAT means E holds in its own ball, so the standard generator (gen_k7_core with explicit
ranges) can produce E's certificate directly; SAT means E is only proved in K's larger ball
(K's own core, renamed by the cube automorphism), which the generator must then take as given.
Also re-checks, for every covered key, that it contains E (orientation, offset) by brute force on
explicit vertex lists, independently of families.contains.  Output data/verify_e.json.

  nice -n 15 python verify_e.py [N]
"""
import sys, os, json, gzip, random, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cores as CO      # noqa: E402
import families as FA   # noqa: E402
k7 = CO.k7


def win(ds):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ 1 << d)
    return vs


def contains_brute(Eds, Erng, K2):
    """Does some orientation/offset of K2's window, as a vertex path, carry E? (directions are
    compared up to a bijection of coordinates, built explicitly)."""
    kind, ds, syms = K2
    cs = FA.cons(kind, syms)
    for o in (0, 1):
        d2 = list(ds) if o == 0 else list(reversed(ds))
        c2 = list(cs) if o == 0 else list(reversed(cs))
        L = len(Eds)
        for i in range(0, len(d2) - L + 1):
            f, g, ok = {}, {}, True
            for a, b in zip(Eds, d2[i:i + L]):
                if f.setdefault(a, b) != b or g.setdefault(b, a) != a:
                    ok = False; break
            if not ok:
                continue
            if all(e is None or (k is not None and e[0] <= k[0] and k[1] <= e[1])
                   for e, k in zip(Erng, c2[i:i + L - 1])):
                return True
    return False


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    S = json.load(gzip.open(os.path.join(HERE, 'data', 'seeds.json.gz'), 'rt'))
    E = S['E']
    rows = []
    for s in S['full']:
        key = json.dumps([s[0], s[1], s[2]])
        e = E.get(key)
        if e is None:
            continue
        n_k = len(s[1])
        bad = [c for c in s[3] if c != [s[0], s[1], s[2]] and
               not contains_brute(tuple(e[0]), [tuple(x) if x else None for x in e[1]],
                                  (c[0], tuple(c[1]), tuple(c[2])))]
        rows.append((s, e, len(s[3]), bad, tuple(e[2]) != (0, n_k)))
    nbad = sum(len(r[3]) for r in rows)
    trimmed = [r for r in rows if r[4] and r[2] > 1]
    random.seed(1)
    sample = random.sample(trimmed, min(n, len(trimmed)))
    wd = os.path.join(CO.SCR, 'work'); os.makedirs(wd, exist_ok=True)
    res = []
    for s, e, ncov, _, _ in sample:
        ds, rng = tuple(e[0]), [tuple(x) if x else None for x in e[1]]
        enc = k7.W.Encoding(win(ds), rng, 4)
        t = time.time()
        st, _, cuts = k7.W.decide(enc, certify=False)
        res.append(dict(seed=s[:3], E_dirs=list(ds), E_ranges=rng, covers=ncov, result=st, cuts=cuts,
                        s=round(time.time() - t, 2)))
        print(st, ncov, ds, rng, flush=True)
    out = dict(seeds=len(rows), covered_pairs=sum(r[2] - 1 for r in rows), brute_force_failures=nbad,
               trimmed_multi=len(trimmed), sample=len(res),
               sample_unsat=sum(r['result'] == 'UNSAT' for r in res), rows=res)
    json.dump(out, open(os.path.join(HERE, 'data', 'verify_e.json'), 'w'), indent=1)
    print({k: v for k, v in out.items() if k != 'rows'})


if __name__ == '__main__':
    main()
