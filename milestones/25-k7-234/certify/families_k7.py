"""Seed plan of the new k7 certificates: which keys are certified, and how every other key follows.

`milestones/30-certificate-families` found that the UNSAT cores of most of the 9,784 new keys of
`../data/keys_best234.json.gz` leave some count bound unused, so one widened certificate implies
sibling keys.  This script turns that finding into the production plan of `gen_k7_core.py`:

* **Widened bounds.**  For a key K = (ds, syms) with core C (`../../30-certificate-families/data/
  cores.jsonl.gz`, CaDiCaL `--seed=1 --unsat`, the first configuration of
  `gen_lean_core.FULL_PORTFOLIO`), the Lean bounds `wide(K)` keep, at centre i, the lower bound of
  `boundOf syms[i]` if C uses the `alpha >= lo` counter of the centre (else 0) and its upper bound
  if C uses `alpha <= hi` (else 21); trailing `(0, 21)` are dropped.  The window is never trimmed,
  so K's own core and LRAT prove `Refuted (winOf ds) (wide K)` (the clause checker `ctrOK` reads
  only the bounds of counters that occur in the core).
* **Implications**, each one decided by the kernel per derived key
  (`work/final_lean/LocalWindowFamilies.lean`):
  - `L1` (`refuted_key_of_wide`): K2 has the same directions and `widerB (wide K) (boundsOf syms2)`;
  - `L2` (`refuted_key_sub`): `subOK (mkPerm v) s (winOf ds) (wide K) (winOf ds2) (boundsOf syms2)`
    for a coordinate permutation list `v` and a translation `s`: the window of K, read forwards or
    backwards at some offset of K2 and relabelled, with every counted range of `wide K` containing
    K2's range there.  `sub_params` searches the offsets and orientations and checks `subOK` with
    an exact Python mirror (`subok`), so every recorded derivation is one the kernel accepts.
* **Seeds**: a weighted greedy set cover of the new keys (cost = the key-set hint estimate plus
  5,000 for the per-window overhead), as `families.py` of milestone 30, but with the untrimmed
  windows only and every implication re-checked by the mirror of the Lean check.

Output `data/seeds234.json.gz`:

  keys     [kind, ds, syms] of every new key, in key-file order
  seeds    [key index, wide bounds] per seed (a seed is also its own first derived key)
  derive   per key: [seed index (into `seeds`), method, v, s]: method 'self' (the seed itself, by L1),
           'L1', or 'L2' (v, s as above; null otherwise)
  summary  counts, hints and the certificate budget (unit costs of README.md)

`gen_k7_core.py run --plan data/seeds234.json.gz` certifies the seeds with their widened bounds
(and re-derives the bounds from its own core, keeping a seed's family only where they still imply
it); `gen_k7_core.py final --plan ...` writes the chunk modules.

  nice -n 15 python3 families_k7.py [--keys ../data/keys_best234.json.gz] [--sample N]
"""
import argparse, collections, gzip, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
M30 = os.path.join(ROOT, 'milestones', '30-certificate-families')
OUT = os.path.join(HERE, 'data', 'seeds234.json.gz')

LUMP = {i: (i, i) for i in range(0, 6)}
LUMP[6] = (6, 21)
TRIV = (0, 21)


# ------------------------------------------------- mirror of the Lean side ---

def bound_of(s):
    """`boundOf` of LocalWindowDirModel."""
    return (s, s) if s < 6 else (6, 21)


def bounds_of(syms):
    return [bound_of(s) for s in syms]


def win_of(ds):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ (1 << d))
    return vs


def lg(n):
    """`Tags.lg n n`."""
    return n.bit_length() - 1 if n >= 1 else 0


def getd(l, i, d):
    return l[i] if 0 <= i < len(l) else d


def centres_k(W, b):
    """`Tags.centresK W b`: (v, d1, d2, lo, hi) per bound."""
    out = []
    for i in range(len(b)):
        c = getd(W, i + 1, 0)
        out.append((c, lg(getd(W, i, 0) ^ c), lg(c ^ getd(W, i + 2, 0)), b[i][0], b[i][1]))
    return out


def wider_b(wide, narrow):
    """`widerB wide narrow`."""
    if len(wide) > len(narrow):
        return False
    return all(w[0] <= n[0] and n[1] <= w[1] for w, n in zip(wide, narrow))


def qfwd(v, x):
    """`(mkPerm v).fwd x` for a permutation list v of 0..8."""
    return v.index(x) if x < 9 else x


def bperm(v, x):
    """`bperm (mkPerm v) x`: bit i of the result is bit `v[i]` of x."""
    return sum(((x >> v[i]) & 1) << i for i in range(9))


def amap(v, s, u):
    return bperm(v, u ^ s)


def subok(v, s, W1, b1, W, b):
    """`subOK (mkPerm v) s W1 b1 W b` of LocalWindowFamilies."""
    if not s < 512:
        return False
    if not all(u < 512 and amap(v, s, u) in W for u in W1):
        return False
    cen = centres_k(W, b)
    for (cv, d1, d2, lo, hi) in centres_k(W1, b1):
        if not (cv < 512 and d1 < 9 and d2 < 9):
            return False
        img = amap(v, s, cv)
        f1, f2 = qfwd(v, d1), qfwd(v, d2)
        ok = any(c[0] == img and ((c[1] == f1 and c[2] == f2) or (c[1] == f2 and c[2] == f1))
                 and lo <= c[3] and c[4] <= hi for c in cen)
        if not (ok or (lo == 0 and 21 <= hi and d1 != d2)):
            return False
    return True


def is_perm9(v):
    return sorted(v) == list(range(9))


def sub_params(cs, wide, ds2, syms2):
    """(v, s) such that `subOK (mkPerm v) s (winOf cs) wide (winOf ds2) (boundsOf syms2)`, or None.
    Tries every offset of `cs` in `ds2`, forwards and backwards."""
    L, n = len(cs), len(ds2)
    W1, W, b = win_of(cs), win_of(ds2), bounds_of(syms2)
    for o in (0, 1):
        for i in range(n - L + 1):
            sl = ds2[i:i + L]
            dirs = sl if o == 0 else sl[::-1]
            fwd = {}
            ok = True
            for c, d in zip(cs, dirs):
                if fwd.setdefault(c, d) != d:
                    ok = False
                    break
            if not ok or len(set(fwd.values())) != len(fwd):
                continue
            v = [None] * 9                         # v[d] = c  <=>  Q.fwd c = d
            for c, d in fwd.items():
                v[d] = c
            rest = [c for c in range(9) if c not in fwd]
            for d in range(9):
                if v[d] is None:
                    v[d] = rest.pop(0)
            base = W[i] if o == 0 else W[i + L]
            s = sum(((base >> d) & 1) << v[d] for d in range(9))
            if subok(v, s, W1, wide, W, b):
                return v, s
    return None


def derivable(seed, wide, key):
    """('L1', None, None) / ('L2', v, s) if the widened seed implies `key`, else None."""
    _, cs, _ = seed
    _, ds2, syms2 = key
    if list(cs) == list(ds2) and wider_b(wide, bounds_of(syms2)):
        return ('L1', None, None)
    p = sub_params(list(cs), wide, list(ds2), list(syms2))
    return ('L2', p[0], p[1]) if p else None


# ------------------------------------------------------ widened bounds ---

def wide_bounds(syms, lo_used, hi_used):
    """Lean bounds of a key whose core uses the lower counters of the centres `lo_used` and the
    upper ones of `hi_used` (0-based centre indices); trailing (0, 21) dropped."""
    out = []
    for i, s in enumerate(syms):
        lo, hi = bound_of(s)
        out.append((lo if i in lo_used else 0, hi if i in hi_used else 21))
    while out and out[-1] == TRIV:
        out.pop()
    return out


def wide_of_record(r):
    """`wide_bounds` from a milestone-30 core record (1-based centre positions `lo`, `hi`)."""
    return wide_bounds(r['syms'], {p - 1 for p in r['lo']}, {p - 1 for p in r['hi']})


# ----------------------------------------------------------------- cover ---

def canon(ds):
    m, r = {}, []
    for d in ds:
        m.setdefault(d, len(m))
        r.append(m[d])
    return tuple(r)


BPH = {'k6': 2.8, 'F': 2.9, 'H': 3.6}


def budget(sel, hints, corecl):
    """CPU hours and GB of `.olean` of the replay + Cnf/Sat modules of the keys `sel` (the unit
    costs of README.md, "Budget of the certificates")."""
    cpu = sum(1 + 0.22e-3 * hints[k] + 6 + 1.2e-3 * 3.6 * corecl[k] for k in sel) / 3600
    gb = sum(37e3 + BPH[k[0]] * hints[k] + 41e3 + 3.5 * 3.6 * corecl[k] for k in sel) / 1e9
    return dict(keys=len(sel), hints=int(sum(hints[k] for k in sel)), cpu_h=round(cpu, 1), olean_GB=round(gb, 2))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--keys', default=os.path.join(HERE, '..', 'data', 'keys_best234.json.gz'))
    ap.add_argument('--cores', default=os.path.join(M30, 'data', 'cores.jsonl.gz'))
    ap.add_argument('--out', default=OUT)
    a = ap.parse_args()
    t0 = time.time()
    d = json.load(gzip.open(a.keys, 'rt'))
    keys, hints, corecl = [], {}, {}
    for k, h, c, b in zip(d['keys'], d['hints'], d['core'], d['basis']):
        if b == 'reuse':
            continue
        kk = (k[0], tuple(k[1]), tuple(k[2]))
        keys.append(kk)
        hints[kk], corecl[kk] = h, c
    rec = {}
    for l in gzip.open(a.cores, 'rt'):
        r = json.loads(l)
        if r['result'] == 'UNSAT':
            rec[(r['kind'], tuple(r['dirs']), tuple(r['syms']))] = r
    wide = {k: wide_of_record(rec[k]) if k in rec else bounds_of(k[2]) for k in keys}
    # candidates: E's window, in either orientation, is a relabelled slice of the key
    byds = collections.defaultdict(list)
    for k in keys:
        byds[canon(k[1])].append(k)
        byds[canon(k[1][::-1])].append(k)
    cover = {k: {k: ('self', None, None)} for k in keys}
    nchk = collections.Counter()
    for k2 in keys:
        ds2 = k2[1]
        n = len(ds2)
        seen = set()
        for L in range(2, n + 1):
            for i in range(0, n - L + 1):
                for src in byds.get(canon(ds2[i:i + L]), ()):
                    if src == k2 or src in seen:
                        continue
                    seen.add(src)
                    nchk['candidates'] += 1
                    dv = derivable(src, wide[src], k2)
                    if dv:
                        cover[src][k2] = dv
                        nchk[dv[0]] += 1
    print('implications', dict(nchk), round(time.time() - t0, 1), 's', flush=True)
    # weighted greedy set cover
    unc, chosen = set(keys), []
    cov = {s: set(v) for s, v in cover.items()}
    while unc:
        best = None
        for s, cv in cov.items():
            live = cv & unc
            if not live:
                continue
            rr = (hints[s] + 5e3) / (sum(hints[x] for x in live) + 5e3 * len(live))
            if best is None or rr < best[0] or (rr == best[0] and s < best[1]):
                best = (rr, s)
        s = best[1]
        live = cov[s] & unc
        chosen.append(s)
        unc -= live
        for t in [t for t, cv in cov.items() if not (cv & unc)]:
            del cov[t]
    sidx = {s: i for i, s in enumerate(chosen)}
    derive = []
    for k in keys:
        # the cheapest chosen seed that implies k (L1 before L2)
        opts = [(0 if cover[s][k][0] in ('self', 'L1') else 1, hints[s], sidx[s], s) for s in chosen
                if k in cover[s]] if k not in sidx else [(0, 0, sidx[k], k)]
        _, _, si, s = min(opts)
        m, v, sv = cover[s][k]
        derive.append([si, m, v, sv])
    meth = collections.Counter(x[1] for x in derive)
    sel = list(chosen)
    tot = budget(keys, hints, corecl)
    seeds_b = budget(sel, hints, corecl)
    l1only = sum(1 for s in chosen)   # noqa: F841 (kept for symmetry with families.py)
    summary = dict(keys=len(keys), with_core=len(rec), seeds=len(chosen), derived=len(keys) - len(chosen),
                   methods=dict(meth), implications=dict(nchk),
                   seeds_widened=sum(1 for s in chosen if [tuple(x) for x in wide[s]] != bounds_of(s[2])),
                   budget_all=tot, budget_seeds=seeds_b,
                   by_kind_seeds=dict(collections.Counter(s[0] for s in chosen)),
                   by_kind_derived=dict(collections.Counter(k[0] for k in keys if k not in sidx)),
                   source=dict(keys=os.path.relpath(a.keys, ROOT), cores=os.path.relpath(a.cores, ROOT)),
                   seconds=round(time.time() - t0, 1))
    out = dict(summary=summary, keys=[[k[0], list(k[1]), list(k[2])] for k in keys],
               seeds=[[keys.index(s), [list(x) for x in wide[s]]] for s in chosen], derive=derive)
    with gzip.GzipFile(a.out, 'wb', mtime=0) as g:
        g.write(json.dumps(out, separators=(',', ':')).encode())
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
