"""Structural implications among the 9,784 new k7 keys (milestone 30, "prove families, not windows").

A key is a window (directions ds, n = len(ds), vertices v0..vn) with a constraint per interior
vertex v1..v(n-1): a lumped symbol s (1..5 exact, 6 = 6..21) or None (uncounted; only the last
interior vertex of an H9 key in its reversed, stored form).

K' implies K by SUB-WINDOW if, in one orientation of K, the directions at some offset i,
relabelled canonically, are K'.ds and every counted centre of K' carries the same symbol in K.
Then any snake window matching K contains a snake window matching K' (the same vertices), so
Refuted K' gives "no snake window matches K".  Reversal and relabelling are built into the
canonical key forms (k6/F8: min over both orientations; H9: one orientation, but a sub-window is
looked up in both orientations of the containing key).

Universes of K':
  set   - the 11,167 keys of keys_best234 (1,383 already certified, free);
  pool  - every known UNSAT k6/F8/H9 key (k7.status + decide234 + oracle_k7/oracle234), with its
          modelled replay cost (prune234.Costs).
Outputs data/classify.json.

  nice -n 15 python classify.py
"""
import sys, os, json, gzip, collections
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
M25 = os.path.join(HERE, '..', '25-k7-234')
sys.path.insert(0, M25)
import k7                      # noqa: E402
import prune234 as P234         # noqa: E402
from refine import canon        # noqa: E402

LUMP = k7.LUMP


def constraints(kind, syms):
    return list(syms) + ([None] if kind == 'H' else [])


def k6form(ds, cs):
    """Canonical k6/F8 form of a fully counted window (min over both orientations)."""
    f = (canon(ds), tuple(cs))
    r = (canon(tuple(reversed(ds))), tuple(reversed(cs)))
    m = min(f, r)
    return ('F' if len(ds) == 8 else 'k6', m[0], m[1])


def subwindows(kind, ds, syms, minlen=3):
    """Every proper sub-window (offset, length) of a key whose interior centres are all counted,
    in canonical form.  Both orientations are covered by k6form (min of the two)."""
    cs = constraints(kind, syms)
    n = len(ds)
    out = []
    for L in range(minlen, n):
        for i in range(0, n - L + 1):
            sub = cs[i:i + L - 1]          # centres v(i+1)..v(i+L-1) -> cs[i]..cs[i+L-2]
            if any(s is None for s in sub):
                continue
            out.append((i, L, k6form(tuple(ds[i:i + L]), sub)))
    return out


def norm(k):
    kind, ds, syms = k
    return (kind, tuple(ds), tuple(syms))


def main():
    d = json.load(gzip.open(os.path.join(M25, 'data', 'keys_best234.json.gz'), 'rt'))
    keys = [norm(k) for k in d['keys']]
    hints = d['hints']; basis = d['basis']
    idx = {k: i for i, k in enumerate(keys)}
    paid = [i for i, b in enumerate(basis) if b != 'reuse']
    S, O, keys6, newk = P234.pool()
    C = P234.Costs(ovh=0.0)
    pool = {}
    for k in keys6:
        h, c, b = C.k6(k)
        pool[('F' if len(k[0]) == 8 else 'k6', k[0], k[1])] = h
    for k in newk:
        h, c, b = C.new(k, O.sec.get(k, 0.05))
        pool[k] = h
    for i, k in enumerate(keys):     # the set's own costs win
        pool[k] = hints[i]

    # (a) sub-window within the set, (a') within the pool
    in_set, in_pool = {}, {}
    for i in paid:
        kind, ds, syms = keys[i]
        subs = subwindows(kind, ds, syms)
        hs = [(o, L, s) for o, L, s in subs if s in idx]
        if hs:
            in_set[i] = [(o, L, list(s[1]), list(s[2]), basis[idx[s]]) for o, L, s in hs]
        hp = [(o, L, s, pool[s]) for o, L, s in subs if s in pool]
        if hp:
            in_pool[i] = hp
    # (b) reversal duplicates: a key whose reversed form (as H9: other orientation) is also a key
    rev_dup = 0
    for i in paid:
        kind, ds, syms = keys[i]
        if kind == 'H':
            continue
        r = k6form(tuple(reversed(ds)), tuple(reversed(syms)))
        if r != keys[i]:
            rev_dup += 1
    # equal windows with different kinds (k6/F8 vs H9 with the same counted part)
    # (c) sibling groups: keys equal except at one centre (count-range lumping candidates)
    sib = collections.defaultdict(list)
    for i in paid:
        kind, ds, syms = keys[i]
        cs = constraints(kind, syms)
        for p, s in enumerate(cs):
            if s is None:
                continue
            sib[(kind, ds, tuple(cs[:p]), tuple(cs[p + 1:]), p)].append((s, i))
    groups = [v for v in sib.values() if len(v) >= 2]

    # seed sets
    implied_set = set(in_set)
    # greedy cover with pool sub-windows: a pool key K' covers every paid key it is a
    # sub-window of; choose by cost per covered hint (weighted set cover), own key as fallback
    cover = collections.defaultdict(set)
    for i, hp in in_pool.items():
        for o, L, s, h in hp:
            cover[s].add(i)
    for i in paid:
        cover[keys[i]].add(i)
    cost = {s: (0.0 if (s in idx and basis[idx[s]] == 'reuse') else pool[s]) for s in cover}
    unc = set(paid); chosen = []; total = 0.0
    while unc:
        best = None
        for s, cv in cover.items():
            g = sum(hints[i] for i in cv & unc) + 1e3 * len(cv & unc)
            if g <= 0:
                continue
            r = (cost[s] + 5e3) / g
            if best is None or r < best[0]:
                best = (r, s)
        s = best[1]
        newly = cover[s] & unc
        unc -= newly; chosen.append((s, len(newly))); total += cost[s]
        for t in list(cover):
            if not (cover[t] & unc):
                del cover[t]
    multi = [(s, n) for s, n in chosen if n > 1]
    paid_hints = sum(hints[i] for i in paid)
    out = dict(
        keys=len(keys), paid=len(paid), paid_hints=paid_hints,
        by_kind=collections.Counter(keys[i][0] for i in paid),
        subwindow_in_set=dict(keys=len(in_set), hints=sum(hints[i] for i in in_set),
                              by_kind=collections.Counter(keys[i][0] for i in in_set),
                              by_implier_basis=collections.Counter(x[4] for v in in_set.values() for x in v[:1]),
                              examples=[[list(keys[i][1]), list(keys[i][2]), keys[i][0], v[0]] for i, v in list(in_set.items())[:10]]),
        seed_set_existing=len(paid) - len(implied_set),
        seed_hints_existing=paid_hints - sum(hints[i] for i in implied_set),
        subwindow_in_pool=dict(keys=len(in_pool), hints=sum(hints[i] for i in in_pool),
                               cheaper=sum(1 for i, hp in in_pool.items() if min(h for *_, h in hp) < hints[i])),
        reversal_noncanonical=rev_dup,
        sibling_groups=dict(n=len(groups), keys=len({i for g in groups for _, i in g}),
                            size_hist=collections.Counter(len(g) for g in groups)),
        greedy_pool_cover=dict(seeds=len(chosen), hints=total, multi_cover_seeds=len(multi),
                               keys_in_multi=sum(n for _, n in multi)),
    )
    print(json.dumps(out, indent=1, default=str))
    json.dump(out, open(os.path.join(HERE, 'data', 'classify.json'), 'w'), indent=1, default=str)
    # sibling groups for the range study
    with gzip.open(os.path.join(HERE, 'data', 'siblings.json.gz'), 'wt') as f:
        json.dump([dict(kind=k[0], dirs=list(k[1]), pre=list(k[2]), post=list(k[3]), pos=k[4],
                        members=[[s, i, hints[i]] for s, i in sorted(v)])
                   for k, v in sib.items() if len(v) >= 2], f)


if __name__ == '__main__':
    main()
