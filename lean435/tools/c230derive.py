#!/usr/bin/env python3
"""Derivations of the 58,817 window exclusions of the K7 chain (milestone 37) from certificates.

    c230derive.py [--out lean435/data/c230derive.json.gz]

Every exclusion e = (dirs, alpha) of `milestones/37-230-feasibility/data/k7_exclusions.json.gz` gets one
source of `Refuted (winOf dirs) alpha` (literal intervals):

  plan   its own certificate `LocalWindowCert.V…` of the 230 plan (c230plan.json.gz, c230.py names)
  sub    a plain key k = (cs, syms) of the 231 plan (certplan231_563_1_cap, Lean-certified in the 231
         audit, its term as in glue435.plain_term) whose window is a contiguous sub-window of
         `winOf dirs`, in either orientation, with containing bounds:
         `Families.refuted_sub (mkPerm v) s <term of k> (by decide +kernel)`.
         (v, s) are computed here and the Bool check `Families.subOK` is evaluated here in Python
         (an exact transcription), so the kernel check cannot fail.

The first covering key in a fixed order is taken (sub-windows longest first, forward before reverse).
"""
import gzip, json, os, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
EXCL = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'k7_exclusions.json.gz')
PLAN230 = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'c230plan.json.gz')
PLAN231 = os.path.join(ROOT, 'milestones', '28-combined-identities', 'data', 'certplan231_563_1_cap.json.gz')


def canon(ds):
    m = {}
    return tuple(m.setdefault(x, len(m)) for x in ds)


def win_of(ds):
    w, cur = [0], 0
    for d in ds:
        cur ^= 1 << d
        w.append(cur)
    return w


def bound_of(s):            # LocalWindowDirModel.boundOf
    return (s, s) if s < 6 else (6, 21)


def lg(n):
    return n.bit_length() - 1


def centres(W, b):          # Tags.centresK
    out = []
    for i in range(len(b)):
        c = W[i + 1] if i + 1 < len(W) else 0
        a = W[i] if i < len(W) else 0
        e = W[i + 2] if i + 2 < len(W) else 0
        out.append((c, lg(a ^ c), lg(c ^ e), b[i][0], b[i][1]))
    return out


def perm_fwd(v):            # mkPerm v for a permutation v of 0..8: fwd (v[i]) = i
    assert sorted(v) == list(range(9))
    f = [0] * 9
    for i, x in enumerate(v):
        f[x] = i
    return f


def amap(f, s, x):          # amap Q s x = bperm Q (x ^^^ s); bit b of the argument goes to bit fwd b
    y, out = x ^ s, 0
    for b in range(9):
        if y >> b & 1:
            out |= 1 << f[b]
    return out


def sub_ok(v, s, W1, b1, W, b):
    """Families.subOK (mkPerm v) s W1 b1 W b."""
    f = perm_fwd(v)
    if not s < 512:
        return False
    if not all(x < 512 and amap(f, s, x) in W for x in W1):
        return False
    C = centres(W, b)
    for (cv, d1, d2, lo, hi) in centres(W1, b1):
        if not (cv < 512 and d1 < 9 and d2 < 9):
            return False
        ok = any(c[0] == amap(f, s, cv) and ({c[1], c[2]} == {f[d1], f[d2]} and
                 ((c[1] == f[d1] and c[2] == f[d2]) or (c[1] == f[d2] and c[2] == f[d1]))) and lo <= c[3] and c[4] <= hi
                 for c in C) or (lo == 0 and 21 <= hi and d1 != d2)
        if not ok:
            return False
    return True


def relabel(seg, cs, Wstart):
    """(v, s) with amap (mkPerm v) s mapping winOf cs onto the walk from vertex Wstart along seg."""
    lab = {}
    for d, l in zip(seg, cs):
        assert lab.setdefault(d, l) == l
    v = [None] * 9
    for d, l in lab.items():
        v[d] = l
    rest = iter(sorted(set(range(9)) - set(lab.values())))
    v = [x if x is not None else next(rest) for x in v]
    s = 0
    for x in range(9):
        if Wstart >> x & 1:
            s |= 1 << v[x]           # bwd x = v[x]
    return v, s


def main():
    out = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else os.path.join(ROOT, 'lean435', 'data', 'c230derive.json.gz')
    ex = json.load(gzip.open(EXCL))['exclusions']
    sys.path.insert(0, HERE)
    import c230
    plan = {(tuple(r['key'][0]), tuple(tuple(b) for b in r['bounds'])): c230.name_of(r['key'])
            for r in json.load(gzip.open(PLAN230))['plain']}
    M = collections.defaultdict(list)
    for r in json.load(gzip.open(PLAN231))['plain']:
        ds, sy = r['key']
        if len(sy) == len(ds) - 1:
            M[tuple(ds)].append(tuple(sy))
    res, cnt = [], collections.Counter()
    for e in ex:
        dirs, al = tuple(e['dirs']), tuple(tuple(b) for b in e['alpha'])
        if (dirs, al) in plan:
            res.append(dict(dirs=list(dirs), alpha=[list(b) for b in al], src='plan', module='LocalWindowCert.' + plan[(dirs, al)]))
            cnt['plan'] += 1
            continue
        n, W, found = len(dirs), win_of(dirs), None
        for L in range(n, 2, -1):
            for i in range(0, n - L + 1):
                j = i + L
                for rev in (False, True):
                    seg = dirs[i:j][::-1] if rev else dirs[i:j]
                    cs = canon(seg)
                    for sy in M.get(cs, ()):
                        bk = [bound_of(x) for x in sy]
                        sub = [al[i + k - 1] for k in range(1, L)] if not rev else [al[j - k - 1] for k in range(1, L)]
                        if all(bl <= lo and hi <= bh for (lo, hi), (bl, bh) in zip(sub, bk)):
                            v, s = relabel(seg, cs, W[j] if rev else W[i])
                            assert sub_ok(v, s, win_of(cs), bk, W, list(al)), (dirs, al, cs, sy, rev, i, j)
                            found = dict(dirs=list(dirs), alpha=[list(b) for b in al], src='sub', key=[list(cs), list(sy)],
                                         perm=v, s=s, i=i, j=j, rev=rev)
                            break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if not found:
            raise SystemExit(f'no source for {dirs} {al}')
        res.append(found)
        cnt['sub'] += 1
    with gzip.GzipFile(out, 'wb', mtime=0) as g:
        g.write(json.dumps(dict(exclusions=res, counts=cnt), separators=(',', ':')).encode())
    print(dict(cnt), out)


if __name__ == '__main__':
    main()
