"""Generate the Lean keys, data, shard and sequence modules of the share-weighted six-centre
automaton WITH CONTEXT SHARES (ctx 7 / ctx 8) from a certificate plan of
milestones/28-combined-identities/certplan231.py, and verify the plan independently.

Copy-and-extend of milestones/33-233-lean/scripts/gen_lean_automaton6s.py (imported for its helpers,
not modified).  Lean side: work/spectral/stronger/WindowAutomaton6SCDefs.lean (`Tables6SC`, `S5C`,
`check6SCAt`, `total_bound6SC`), WindowAutomaton6SCV2.lean (`check6SCAtW`, witness codes 13/14),
DirectionWindowBridge6SC.lean (`RefutedCtx7/8`, `CtxCover`), AggregateDirection6SCConditional.lean;
design in milestones/35-231-lean/DESIGN.md.

The step test (one potential, as in 233):

    P + pot(next) <= Q (120 s + S5C) + pot(current),   S5C = max(L5 fw, L5 rv, ctx7, ctx8)

on every transition not excluded by a plain k6 key (3..7 directions ending at the new vertex, both
orientations) or an H8 cut.  ctx7 = C7[canon(d(n+1..n+7))][t], ctx8 = C8[canon(d(n..n+7))][t], with
t = the six lumped counts a(n+2..n+7) (oriented, no reversed lookup).

Input: a plan `certplan231_<tag>.json.gz`:
  plain  {key: [dirs, lumped syms], free, basis}      -> k6 exclusion table, `Refuted` keys (all of them;
                                                          `free` only says the certificate exists)
  share  {kind: '5' | 'c7' | 'c8', key: [dirs, t], level, basis, free}
         '5'  : 5-window share field (6 directions, 5 counts).  basis 'lean_floor' -> must satisfy
                level <= floorLevel (main's floors, Floors233); basis 'free233' -> the 233 share key
                (keys233_best.json.gz) with T233 >= level is reused verbatim as (dirs, t, T233 - 1);
                otherwise a new share key (dirs, t, level - 1)
         'c7' : ctx 7 field: key (canon 7 dirs, 6 counts) -> RefutedCtx7 (dirs, t, level - 1)
         'c8' : ctx 8 field: key (canon 8 dirs, 6 counts of the vertices n+2..n+7) -> RefutedCtx8 (..)
  h8     not in the plan format of 15 November: certplan231.World231 adds all 262 H8 cuts of the 233
         chain as free and never drops them, so they are read from keys233_best.json.gz (or from a
         top-level 'h8' list of the plan, if a later plan has one).

Verification (nothing of the plan's potential is used): Bellman-Ford from scratch on the canonical
labels for lambda = P/Q with the decoded tables; the potential must fit the plan's B bits; then every
transition of every label below 9 is re-checked against the decoded tables while choosing its
witness code (0 / 12 inequality with the forward / reversed 5-window field, 13 / 14 with the ctx 7 /
ctx 8 field, 1..10 k6 window, 11 H8); the bound (P + 4200 Q) m <= 1099800 Q + 7 P + 2^B - 1 must
give --expect-bound (default 231).  Any failure aborts.

Outputs (identifiers carry the tag T):
  <out-core>/LocalWindowDirKeys6SC<T>P<g>.lean   plain key chunks (parts of --part-chunks chunks)
  <out-core>/LocalWindowDirKeys6SC<T>.lean       dirChunks6S<T>, h8Keys6S<T>, shareKeys6S<T>,
                                                 ctx7Chunks6SC<T>, ctx8Chunks6SC<T>,
                                                 AllRefuted6S<T>, AllRefutedShare6S<T>, AllRefutedCtx6SC<T>
  <out>/WindowAutomaton6SC<T>Data.lean           tables6SC<T> (k6 + H8 + 5-window share + ctx 7 + ctx 8)
  <out>/WindowAutomaton6SC<T>Shard<i>_<t0>.lean  204 shards (`check6SCAtW`, nat_lit witness literals)
  <out>/WindowAutomaton6SC<T>Sequence.lean       stepOK6SC<T> : StepOK6SC tables6SC<T>
  <summary>                                      json for gen_lean_chain6sc.py

  python gen_lean_automaton6sc.py --plan PLAN.json.gz --tag T --out-stronger DIR --out-core DIR [--dry-run]
  --shards all|none|i_t0,...  ; --stub-shards writes `sorry` stubs for the others (scratch only).
"""
import argparse, gzip, hashlib, json, os, sys, time
from fractions import Fraction as Fr
sys.dont_write_bytecode = True
import numpy as np
sys.set_int_max_str_digits(0)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '33-233-lean', 'scripts'))
import gen_lean_automaton6s as G6   # noqa: E402  (helpers only; the 233 generator is not modified)
GA = G6.GA
DATA = os.path.join(HERE, '..', 'data')
ME = 'milestones/35-231-lean/scripts/gen_lean_automaton6sc.py'
KEYS233 = os.path.join(ROOT, 'milestones', '31-233-cost', 'data', 'keys233_best.json.gz')
NC, NT = 6 ** 5, 6 ** 6
canon, induced, shape_code, lst, tree, ntree, nib_lit, pack, field = (
    GA.canon, GA.induced, GA.shape_code, G6.lst, G6.tree, G6.ntree, G6.nib_lit, G6.pack, G6.field)


def load_plan(path):
    d = json.load(gzip.open(path, 'rt') if path.endswith('.gz') else open(path))
    s = d['summary']
    plain = sorted({(tuple(r['key'][0]), tuple(r['key'][1])) for r in d['plain']}, key=lambda k: (len(k[0]), k))
    assert len(plain) == len(d['plain']), 'duplicate plain keys in the plan'
    for c, t in plain:
        assert GA.is_rgs(c) and 3 <= len(c) <= 7 and len(t) + 1 == len(c) and all(1 <= x <= 6 for x in t), (c, t)
    k233 = json.load(gzip.open(KEYS233, 'rt'))
    if 'h8' in d:
        h8src, h8raw = 'plan', d['h8']
    else:
        h8src, h8raw = 'keys233_best.json.gz (all 262 H8 cuts of the 233 chain; certplan231 keeps them all)', k233['h8']
    h8 = sorted({(tuple(k[0]), tuple(k[1])) for k in h8raw}, key=lambda k: G6.enc(9, k[0] + k[1]))
    for c, t in h8:
        assert GA.is_rgs(c) and len(c) == 8 and len(t) == 6 and all(1 <= x <= 6 for x in t), (c, t)
    s233 = {}
    for ds, sy, T, lb, b, h in k233['share']:
        if b != 'lean_floor':
            s233[(tuple(ds), tuple(sy))] = max(s233.get((tuple(ds), tuple(sy)), 0), int(T))
    share, skeys, c7, c8 = {}, {}, {}, {}
    nfree233 = 0
    for r in d['share']:
        c, t, L, b = tuple(r['key'][0]), tuple(r['key'][1]), int(r['level']), r['basis']
        assert L > 0 and GA.is_rgs(c) and all(1 <= x <= 6 for x in t), r
        if r['kind'] == '5':
            assert len(c) == 6 and len(t) == 5 and (c, t) not in share, r
            share[(c, t)] = (L, b)
            if b == 'lean_floor':
                assert L <= G6.floor_level(c, t), ('floor entry above the Lean floor', r)
            elif L > G6.floor_level(c, t):
                if b == 'free233':
                    T233 = s233.get((c, t))
                    assert T233 is not None and T233 >= L, ('free233 entry without a 233 share key at >= level', r)
                    skeys[(c, t)] = T233 - 1; nfree233 += 1
                else:
                    assert not r['free'], r
                    skeys[(c, t)] = L - 1
        elif r['kind'] in ('c7', 'c8'):
            n = 7 if r['kind'] == 'c7' else 8
            X = c7 if n == 7 else c8
            assert len(c) == n and len(t) == 6 and (c, t) not in X and not r['free'], r
            X[(c, t)] = L
        else:
            raise SystemExit(f'unknown share kind {r["kind"]}')
    return dict(summary=s, plain=plain, plain_rows=d['plain'], h8=h8, h8src=h8src, share=share,
                skeys=sorted((c, t, k) for (c, t), k in skeys.items()), nfree233=nfree233, c7=c7, c8=c8)


class Tabs6SC(G6.Tabs):
    """The 6S tables plus the two ctx tables, decoded back from the packed rows."""

    def __init__(self, plain, h8, share, sbits, c7, c8, cbits):
        super().__init__(plain, h8, share, sbits)
        self.cbits = cbits
        self.ctx = {}
        for n, X in ((7, c7), (8, c8)):
            shapes = sorted({c for c, t in X})
            idx = {shape_code(c): i for i, c in enumerate(shapes)}
            arr = {c: np.zeros((6,) * 6, np.int64) for c in shapes}
            for (c, t), L in X.items():
                arr[c][tuple(x - 1 for x in t)] = L
            rows = {}
            for c in shapes:
                for t0 in range(1, 7):
                    v = arr[c][t0 - 1].ravel()
                    if v.any():
                        rows[(idx[shape_code(c)], t0)] = pack(v, cbits)
            dec = {}
            for (r, t0), row in rows.items():
                c = shapes[r]
                A = dec.setdefault(c, np.zeros((6,) * 6, np.int64))
                A[t0 - 1] = np.array([field(row, cbits, k) for k in range(NC)]).reshape((6,) * 5)
            for (c, t), L in X.items():
                assert dec[c][tuple(x - 1 for x in t)] == L, 'ctx decoding mismatch'
            assert sum(int((A > 0).sum()) for A in dec.values()) == len(X), 'ctx decoding mismatch (extra fields)'
            self.ctx[n] = dict(shapes=shapes, idx=idx, rows=rows, dec=dec)

    def ctxs(self, X):
        """ctx 7 and ctx 8 fields of the step window X (8 directions), over 6^6."""
        z = np.zeros(NT, np.int64)
        a7 = self.ctx[7]['dec'].get(canon(X[1:8]))
        a8 = self.ctx[8]['dec'].get(canon(X))
        return (z if a7 is None else a7.ravel()), (z if a8 is None else a8.ravel())


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--plan', required=True)
    ap.add_argument('--tag', required=True)
    ap.add_argument('--lam', help='override the plan lambda P/Q')
    ap.add_argument('--bits', type=int, help='override the plan potential bits B')
    ap.add_argument('--cbits', type=int, default=None, help='ctx field width (default: from the levels)')
    ap.add_argument('--expect-bound', type=int, default=231)
    ap.add_argument('--max-iter', type=int, default=5000)
    ap.add_argument('--chunk', type=int, default=400)
    ap.add_argument('--part-chunks', type=int, default=16, help='plain key chunks per keys part module')
    ap.add_argument('--shards', default='all')
    ap.add_argument('--stub-shards', action='store_true')
    ap.add_argument('--out-stronger', required=True)
    ap.add_argument('--out-core', required=True)
    ap.add_argument('--summary', default=None)
    ap.add_argument('--sha256', default=None, help='write sha256 of the data module and shards here')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    T = a.tag
    t_start = time.time()
    pl = load_plan(a.plan)
    ps = pl['summary']
    plain, h8, share, skeys, c7, c8 = pl['plain'], pl['h8'], pl['share'], pl['skeys'], pl['c7'], pl['c8']
    lam = Fr(a.lam) if a.lam else Fr(ps['P'], ps['Q'])
    P, Q = lam.numerator, lam.denominator
    B = a.bits or ps['B']
    sbits = max(L for L, _ in share.values()).bit_length()
    cmax = max(list(c7.values()) + list(c8.values()) + [1])
    cbits = a.cbits or cmax.bit_length()
    assert cmax < 2 ** cbits, f'ctx level {cmax} does not fit {cbits} bits'
    tb = Tabs6SC(plain, h8, share, sbits, c7, c8, cbits)
    shp = GA.shapes7()
    s7 = {c: i for i, c in enumerate(shp)}
    assert len(shp) == 34
    k7 = sorted((c, t, L - 1) for (c, t), L in c7.items())
    k8 = sorted((c, t, L - 1) for (c, t), L in c8.items())
    print(f'plan {os.path.basename(a.plan)}: lambda = {P}/{Q}, B = {B}; {len(plain)} plain keys '
          f'({sum(1 for r in pl["plain_rows"] if r["free"])} free), {len(h8)} H8 keys ({pl["h8src"]}), '
          f'{len(share)} 5-window fields ({sbits} bits; {len(skeys)} share keys, {pl["nfree233"]} of them reused '
          f'233 keys), {len(c7)} ctx 7 and {len(c8)} ctx 8 keys (max level {cmax}, {cbits}-bit fields); '
          f'{len(tb.wshapes)} window shapes, {len(tb.forb)} exclusion rows, {len(tb.shr)} share rows, '
          f'{len(tb.ctx[7]["rows"])} / {len(tb.ctx[8]["rows"])} ctx rows on {len(tb.ctx[7]["shapes"])} / '
          f'{len(tb.ctx[8]["shapes"])} shapes', flush=True)
    for c in tb.ctx[7]['shapes']:
        assert induced(c), ('ctx 7 shape not induced', c)
    for c in tb.ctx[8]['shapes']:
        assert induced(c), ('ctx 8 shape not induced', c)

    x = np.arange(NT)
    s = x % 6 + 1

    def level(X):
        fw, rv = tb.shares(X)
        a7, a8 = tb.ctxs(X)
        return fw, rv, a7, a8

    # Bellman-Ford on the canonical labels, from scratch
    Us, Vs, Ws = [], [], []
    for i, c in enumerate(shp):
        for d in range(min(max(c) + 2, 9)):
            X = c + (d,)
            if not induced(X):
                continue
            j = s7[canon(X[1:])]
            ok = tb.codes(X) == 0
            fw, rv, a7, a8 = level(X)
            w = Q * (120 * s + np.maximum(np.maximum(fw, rv), np.maximum(a7, a8))) - P
            Us.append(i * NC + x[ok] // 6); Vs.append(j * NC + x[ok] % NC); Ws.append(w[ok])
    U, V, W = np.concatenate(Us), np.concatenate(Vs), np.concatenate(Ws)
    del Us, Vs, Ws
    ntrans = len(U)
    print(f'{34 * NC} states, {ntrans} allowed transitions (canonical labels); Bellman-Ford for lambda = {P}/{Q}',
          flush=True)
    pi, iters = G6.bellman_ford(34 * NC, U, V, W, a.max_iter)
    if pi is None:
        raise SystemExit(f'PLAN REJECTED: no potential after {iters} rounds (a negative cycle at lambda = {P}/{Q})')
    pi = pi - pi.min()
    rng = int(pi.max())
    if rng >= 2 ** B:
        raise SystemExit(f'PLAN REJECTED: potential range {rng} does not fit {B} bits')
    del U, V, W
    pots = {}
    for i in range(34):
        for t0 in range(1, 7):
            base = i * NC + (t0 - 1) * 6 ** 4
            pots[(i, t0)] = pack(pi[base:base + 6 ** 4], B)
    dpi = np.zeros(34 * NC, np.int64)
    for (i, t0), row in pots.items():
        base = i * NC + (t0 - 1) * 6 ** 4
        dpi[base:base + 6 ** 4] = [field(row, B, k) for k in range(6 ** 4)]
    assert (dpi == pi).all()
    # re-check of every transition of every label below 9 against the decoded tables; witness codes
    witness, census, ntr = {}, np.zeros(16, np.int64), 0
    for i, c in enumerate(shp):
        for d in range(9):
            X = c + (d,)
            if not induced(X):
                continue
            j = s7[canon(X[1:])]
            wc = tb.codes(X)
            fw, rv, a7, a8 = level(X)
            src, dst = dpi[i * NC + x // 6], dpi[j * NC + x % NC]
            ok = [P + dst <= Q * (120 * s + L) + src for L in (fw, rv, a7, a8)]
            code = np.where(ok[0], 0, np.where(ok[1], 12, np.where(ok[2], 13, np.where(ok[3], 14, wc)))).astype(np.int8)
            bad = ~ok[0] & ~ok[1] & ~ok[2] & ~ok[3] & (wc == 0)
            if bad.any():
                raise SystemExit(f'PLAN REJECTED: {int(bad.sum())} transitions of the label {X} without a witness')
            witness[(i, d)] = code
            census += np.bincount(code, minlength=16)
            ntr += NT
    R = 2 ** B - 1
    N = (1099800 * Q + 7 * P + R) // (P + 4200 * Q)
    print(f'potential range {rng} ({B} bits; plan says {ps.get("range")}), {iters} rounds; re-check passed on '
          f'{ntr} transitions (all labels); witness codes {dict((k, int(v)) for k, v in enumerate(census) if v)}',
          flush=True)
    print(f'bound: ({P} + 4200*{Q}) m <= 1099800*{Q} + 7*{P} + {R} = {1099800 * Q + 7 * P + R}, so m <= {N}',
          flush=True)
    if N != a.expect_bound:
        raise SystemExit(f'PLAN REJECTED: the bound is {N}, not {a.expect_bound}')

    # chunks of whole exclusion rows for the k6 cover
    rows_by = {}
    for k in plain:
        rows_by.setdefault((k[0], k[1][0]), []).append(k)
    chunks, where, cur = [], {}, []
    for r in sorted(rows_by, key=lambda r: (len(r[0]), r)):
        if cur and len(cur) + len(rows_by[r]) > a.chunk:
            chunks.append(cur); cur = []
        where[r] = len(chunks)
        cur = cur + rows_by[r]
    if cur or not chunks:
        chunks.append(cur)
    rowlist = sorted(((tb.wshapes[r], s0) for (r, s0), m in tb.forb.items() if m), key=lambda r: (len(r[0]), r))
    ctxsh = {n: tb.ctx[n]['shapes'] for n in (7, 8)}
    ctxch = {7: [[k for k in k7 if k[0] == c] for c in ctxsh[7]], 8: [[k for k in k8 if k[0] == c] for c in ctxsh[8]]}
    nparts = (len(chunks) + a.part_chunks - 1) // a.part_chunks
    summary = dict(tag=T, plan=os.path.relpath(os.path.abspath(a.plan), ROOT),
                   plan_sha256=hashlib.sha256(open(a.plan, 'rb').read()).hexdigest(),
                   plain_keys=len(plain), plain_free=sum(1 for r in pl['plain_rows'] if r['free']),
                   plain_by_basis={b: sum(1 for r in pl['plain_rows'] if r['basis'] == b)
                                   for b in sorted({r['basis'] for r in pl['plain_rows']})},
                   h8_keys=len(h8), h8_source=pl['h8src'], share_fields=len(share), share_keys=len(skeys),
                   share_keys_reused233=pl['nfree233'], share_on_floors=len(share) - len(skeys), sbits=sbits,
                   ctx7_keys=len(k7), ctx8_keys=len(k8), cbits=cbits, ctx_max_level=cmax,
                   ctx7_rows=len(tb.ctx[7]['rows']), ctx8_rows=len(tb.ctx[8]['rows']),
                   P=P, Q=Q, bits=B, potential_range=rng, plan_range=ps.get('range'), bound=N, toy=False,
                   bf_rounds=iters, allowed_transitions_canonical=ntrans, transitions_checked=ntr,
                   witness_census={str(k): int(v) for k, v in enumerate(census) if v},
                   k_chunks=len(chunks), key_parts=nparts, part_chunks=a.part_chunks,
                   rows=[[list(c), s0, where[(c, s0)]] for c, s0 in rowlist],
                   share_shapes=[list(c) for c in tb.sshapes],
                   ctx7_shapes=[list(c) for c in ctxsh[7]], ctx8_shapes=[list(c) for c in ctxsh[8]],
                   seconds=round(time.time() - t_start))
    if a.dry_run:
        print(json.dumps({k: v for k, v in summary.items()
                          if k not in ('rows', 'share_shapes', 'ctx7_shapes', 'ctx8_shapes')}), flush=True)
        return
    out = {}
    nc = 'noncomputable '
    for g in range(nparts):
        cis = range(g * a.part_chunks, min(len(chunks), (g + 1) * a.part_chunks))
        out[os.path.join(a.out_core, f'LocalWindowDirKeys6SC{T}P{g}.lean')] = f'''/-! Plain k6 key chunks {cis[0]} .. {cis[-1]} of the automaton `{T}` (generated by `{ME}`). -/

namespace Snake9.LocalWindow

''' + ''.join(f'''{nc}def dirChunk6S{T}_{ci} : List (List Nat × List Nat) := [
''' + ',\n'.join(f'  ({lst(d)}, {lst(t)})' for d, t in chunks[ci]) + ''']

''' for ci in cis) + 'end Snake9.LocalWindow\n'

    def klist(name, ks):
        return f'''{nc}def {name} : List (List Nat × List Nat × Nat) := [
''' + ',\n'.join(f'  ({lst(d)}, {lst(t)}, {k})' for d, t, k in ks) + ''']

'''
    keys_mod = (''.join(f'import LocalWindowDirKeys6SC{T}P{g}\n' for g in range(nparts)) + f'''import DirectionWindowBridge6SC

/-!
# Certificate keys of the share-weighted six-centre automaton with context shares `{T}`

Generated by `{ME}` from the plan `{summary["plan"]}`
(sha256 {summary["plan_sha256"][:16]}...).

* `dirChunks6S{T}`: {len(plain)} plain k6 keys `(dirs, lumped syms)` ({summary["plain_free"]} of them have a
  certificate already: 233 chain, 235-237 replays, or L1/L2 from a 233 seed), chunks of whole exclusion rows;
  certificate `Refuted (winOf dirs) (boundsOf syms)`.
* `h8Keys6S{T}`: {len(h8)} H8 keys (the 233 chain's); certificate `Refuted (winOf dirs) (boundsOf syms)`.
* `shareKeys6S{T}`: {len(skeys)} 5-window share thresholds `(dirs, syms, K)` ({pl["nfree233"]} of them the 233
  chain's own keys); certificate `RefutedShare (winOf dirs) (boundsOf syms) 12 K`.  The other
  {len(share) - len(skeys)} 5-window fields are covered by main's floor theorems (`Floors233`).
* `ctx7Chunks6SC{T}`: {len(k7)} ctx 7 keys `(dirs, t, K)`, one chunk per shape; certificate `RefutedCtx7`.
* `ctx8Chunks6SC{T}`: {len(k8)} ctx 8 keys, one chunk per shape; certificate `RefutedCtx8`.
-/

set_option maxHeartbeats 0

namespace Snake9.LocalWindow
open Snake9.DirectionWindow6S Snake9.DirectionWindow6SC

{nc}def dirChunks6S{T} : List (List (List Nat × List Nat)) :=
  [{', '.join(f'dirChunk6S{T}_{ci}' for ci in range(len(chunks)))}]

{nc}def dirKeys6S{T} : List (List Nat × List Nat) := dirChunks6S{T}.flatten

{nc}def h8Keys6S{T} : List (List Nat × List Nat) := [
''' + ',\n'.join(f'  ({lst(d)}, {lst(t)})' for d, t in h8) + f''']

''' + klist(f'shareKeys6S{T}', skeys)
        + ''.join(klist(f'ctx{n}Chunk6SC{T}_{k}', ch) for n in (7, 8) for k, ch in enumerate(ctxch[n]))
        + ''.join(f'''{nc}def ctx{n}Chunks6SC{T} : List (List (List Nat × List Nat × Nat)) :=
  [{', '.join(f'ctx{n}Chunk6SC{T}_{k}' for k in range(len(ctxch[n])))}]

{nc}def ctx{n}Keys6SC{T} : List (List Nat × List Nat × Nat) := ctx{n}Chunks6SC{T}.flatten

''' for n in (7, 8)) + f'''/-- The plain and H8 certificate statements. -/
def AllRefuted6S{T} : Prop := AllRefutedList dirKeys6S{T} ∧ AllRefutedList h8Keys6S{T}

/-- The 5-window share certificate statements. -/
def AllRefutedShare6S{T} : Prop := AllRefutedShareList shareKeys6S{T}

/-- The context share certificate statements (ctx 7 and ctx 8). -/
def AllRefutedCtx6SC{T} : Prop := AllP RefutedCtx7 ctx7Keys6SC{T} ∧ AllP RefutedCtx8 ctx8Keys6SC{T}

end Snake9.LocalWindow
''')
    out[os.path.join(a.out_core, f'LocalWindowDirKeys6SC{T}.lean')] = keys_mod
    witems = sorted((cd, str(i)) for cd, i in tb.widx.items())
    fitems = sorted((r * 7 + s0, f'0x{m:x}') for (r, s0), m in tb.forb.items() if m)
    pitems = sorted((shape_code(c), str(i)) for i, c in enumerate(shp))
    sitems = sorted((cd, str(i)) for cd, i in tb.sidx.items())
    defs, sel = [], []
    for i in range(34):
        it = sorted((t0, f'0x{pots[(i, t0)]:x}') for t0 in range(1, 7) if pots[(i, t0)])
        if it:
            defs.append(f'def potRow6SC{T}_{i} (t0 : Nat) : Nat :=\n  {tree("t0", it, "0")}\n')
            sel.append((i, f'potRow6SC{T}_{i} t0'))
    potdef = ('\n'.join(defs) + f'\ndef potMask6SC{T} (r t0 : Nat) : Nat :=\n  {tree("r", sel, "0")}')
    sdefs, ssel = [], []
    for r in range(len(tb.sshapes)):
        it = sorted((t0, f'0x{tb.shr[(r, t0)]:x}') for t0 in range(1, 7) if tb.shr.get((r, t0)))
        if it:
            sdefs.append(f'def shrRow6SC{T}_{r} (t0 : Nat) : Nat :=\n  {tree("t0", it, "0")}\n')
            ssel.append((r, f'shrRow6SC{T}_{r} t0'))
    shrdef = '\n'.join(sdefs) + f'\ndef shrMask6SC{T} (r t0 : Nat) : Nat :=\n  {tree("r", ssel, "0")}'
    cdefs = []
    for n in (7, 8):
        X = tb.ctx[n]
        items = sorted((shape_code(c), str(i)) for i, c in enumerate(X['shapes']))
        cdefs.append(f'''/-- Canonical {n}-direction ctx {n} shapes ↦ ctx {n} row. -/
def c{n}Idx6SC{T} (c : Nat) : Nat :=
  {tree("c", items, str(len(X['shapes'])))}
''')
        rsel = []
        for r in range(len(X['shapes'])):
            it = sorted((t0, f'0x{X["rows"][(r, t0)]:x}') for t0 in range(1, 7) if X['rows'].get((r, t0)))
            if it:
                cdefs.append(f'def c{n}Row6SC{T}_{r} (t0 : Nat) : Nat :=\n  {tree("t0", it, "0")}\n')
                rsel.append((r, f'c{n}Row6SC{T}_{r} t0'))
        cdefs.append(f'''/-- ctx {n} rows: (shape, first count t0) ↦ {cbits}-bit fields at `cntIdx6` of the other five. -/
def c{n}Rows6SC{T} (r t0 : Nat) : Nat :=
  {tree("r", rsel, "0")}
''')
    data = f'''/-
Generated by {ME}.  Do not edit by hand.
Share-weighted six-centre automaton with context shares `{T}` from the plan `{summary["plan"]}`:
{len(plain)} plain keys, {len(h8)} H8 keys, {len(share)} 5-window share fields ({sbits} bits), {len(c7)} ctx 7 and
{len(c8)} ctx 8 fields ({cbits} bits); lambda = {P}/{Q} (weight units, 120 per alpha unit), potential on
{34 * NC} states, range {rng} ({B}-bit fields); bound m <= {N}.
-/
import WindowAutomaton6SCDefs

set_option maxHeartbeats 0

namespace Snake9.WindowAutomaton

/-- Canonical window shapes (3 to 7 directions) ↦ exclusion row. -/
def wIdx6SC{T} (c : Nat) : Nat :=
  {tree("c", witems, str(len(tb.wshapes)))}

/-- Exclusion rows: `7 * row + first count` ↦ mask over `symIdx` of the other counts. -/
def forbRows6SC{T} (k : Nat) : Nat :=
  {tree("k", fitems, "0")}

def forbMask6SC{T} (r s : Nat) : Nat := forbRows6SC{T} (r * 7 + s)

/-- Canonical induced 7-direction shapes ↦ potential row. -/
def pIdx6SC{T} (c : Nat) : Nat :=
  {tree("c", pitems, "34")}

/-- Potential rows: (7-shape, first count) ↦ {B}-bit fields at `cntIdx6` of the other four. -/
{potdef}

/-- 6-direction share shapes ↦ share row. -/
def sIdx6SC{T} (c : Nat) : Nat :=
  {tree("c", sitems, str(len(tb.sshapes)))}

/-- Share rows: (share shape, first count) ↦ {sbits}-bit fields at `cntIdx6` of the other four. -/
{shrdef}

/-- The H8 keys: `encB 9 (dirs ++ syms) 0`, in order. -/
def h8Tree6SC{T} : NTree :=
  {ntree(tb.hcodes)}

{chr(10).join(cdefs)}
def tables6SC{T}k6 : Tables6 where
  wIdx := wIdx6SC{T}
  forb := forbMask6SC{T}
  pIdx := pIdx6SC{T}
  pot := potMask6SC{T}
  bits := {B}
  num := {P}
  den := {Q}

def tables6SC{T}S : Tables6S where
  k6 := tables6SC{T}k6
  htree := h8Tree6SC{T}
  sIdx := sIdx6SC{T}
  shr := shrMask6SC{T}
  sbits := {sbits}

def tables6SC{T} : Tables6SC where
  s := tables6SC{T}S
  c7Idx := c7Idx6SC{T}
  c7 := c7Rows6SC{T}
  c8Idx := c8Idx6SC{T}
  c8 := c8Rows6SC{T}
  cbits := {cbits}

def shapes7_6SC{T} : List (List Nat) := [{', '.join(lst(c) for c in shp)}]

/-- The nonzero exclusion rows (window shape, first count), for `cover6_chunks`. -/
def rows6SC{T} : List (List Nat × Nat) := [{', '.join(f'({lst(c)}, {s0})' for c, s0 in rowlist)}]

/-- The share shapes with a nonzero row, for `shareCover_rows`. -/
def sshapes6SC{T} : List (List Nat) := [{', '.join(lst(c) for c in tb.sshapes)}]

/-- The ctx 7 / ctx 8 shapes with a nonzero row, for `ctxCover_rows` (chunk `i` of the keys is shape `i`). -/
def ctx7Shapes6SC{T} : List (List Nat) := [{', '.join(lst(c) for c in ctxsh[7])}]
def ctx8Shapes6SC{T} : List (List Nat) := [{', '.join(lst(c) for c in ctxsh[8])}]

end Snake9.WindowAutomaton
'''
    out[os.path.join(a.out_stronger, f'WindowAutomaton6SC{T}Data.lean')] = data
    want = None if a.shards == 'all' else (set() if a.shards == 'none' else
                                            {tuple(map(int, q.split('_'))) for q in a.shards.split(',')})
    shard_paths = []
    for i, c in enumerate(shp):
        for t0 in range(1, 7):
            p = os.path.join(a.out_stronger, f'WindowAutomaton6SC{T}Shard{i}_{t0}.lean')
            head = f'''/-
Generated by {ME}.  Shard ({i}, {t0}) of the step table of `tables6SC{T}`:
canonical 7-shape {lst(c)} extended by every label below 9, first count {t0}.'''
            stmt = f'allBelow 9 (fun d => check6SCAt tables6SC{T} ({lst(c)} ++ [d]) {t0}) = true'
            if want is not None and (i, t0) not in want:
                if a.stub_shards:
                    out[p] = f'''{head}
STUB (scratch build only, never commit): the statement is assumed.
-/
import WindowAutomaton6SC{T}Data

namespace Snake9.WindowAutomaton

theorem shard6SC{T}_{i}_{t0} : {stmt} := sorry

end Snake9.WindowAutomaton
'''
                continue
            decls = []
            for d in range(9):
                X = c + (d,)
                nm = f'shard6SC{T}_{i}_{t0}_{d}'
                cc = f'({lst(c)} ++ [{d}])'
                if induced(X):
                    code = witness[(i, d)][(t0 - 1) * NC:t0 * NC]
                    decls.append(f'''set_option maxRecDepth 100000 in
theorem {nm}_w : check6SCAtW tables6SC{T} {cc} {t0}
    (nat_lit {nib_lit(code)}) = true := by
  decide +kernel

theorem {nm} : check6SCAt tables6SC{T} {cc} {t0} = true := check6SCAt_of_W _ _ _ _ {nm}_w
''')
                else:
                    decls.append(f'''theorem {nm} : check6SCAt tables6SC{T} {cc} {t0} = true := by
  decide +kernel -- not induced: no transition
''')
            out[p] = f'''{head}
One witness-driven kernel check (`check6SCAtW`, WindowAutomaton6SCV2) per label: a 4-bit code per
transition chooses the disjunct the kernel evaluates (0/12 the 5-window share field forward/reversed,
13/14 the ctx 7/ctx 8 field, 1..11 an excluding window); `check6SCAt_of_W` gives `check6SCAt`
whatever the codes.
-/
import WindowAutomaton6SC{T}Data
import WindowAutomaton6SCV2

set_option Elab.async false

namespace Snake9.WindowAutomaton

{chr(10).join(decls)}
theorem shard6SC{T}_{i}_{t0} : {stmt} :=
  allBelow9_of _ {' '.join(f'shard6SC{T}_{i}_{t0}_{d}' for d in range(9))}

end Snake9.WindowAutomaton
'''
            shard_paths.append(p)
    imports = '\n'.join(f'import WindowAutomaton6SC{T}Shard{i}_{t0}' for i in range(34) for t0 in range(1, 7))
    shape_lemmas = '\n\n'.join(f'''theorem shape6SC{T}_{i} : ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    allBelow 9 (fun d => check6SCAt tables6SC{T} ({lst(c)} ++ [d]) t0) = true := by
  intro t0 h1 h6
  have : t0 = 1 ∨ t0 = 2 ∨ t0 = 3 ∨ t0 = 4 ∨ t0 = 5 ∨ t0 = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
{chr(10).join(f'  · exact shard6SC{T}_{i}_{t0}' for t0 in range(1, 7))}''' for i, c in enumerate(shp))
    pres = GA.rgs(5)
    pre_lemmas = '\n\n'.join(f'''set_option maxRecDepth 100000 in
theorem shapesPre6SC{T}_{j} :
    allRGS 3 (rgsBound {lst(q)} 0) (fun l => shapeTest6 shapes7_6SC{T} ({lst(q)} ++ l)) = true := by
  decide +kernel''' for j, q in enumerate(pres))
    seq = f'''/-
Generated by {ME}.
Combines the {6 * len(shp)} shards of `tables6SC{T}` into `StepOK6SC tables6SC{T}`.
-/
{imports}

set_option Elab.async false

namespace Snake9.WindowAutomaton

{pre_lemmas}

theorem shapesCover6SC{T} : ShapesCover shapes7_6SC{T} = true :=
  shapesCover_of _ [{', '.join(lst(q) for q in pres)}] 5 3 rfl (by decide +kernel) (by
    intro pre h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with {' | '.join(['rfl'] * len(pres))}
{chr(10).join(f'    · exact shapesPre6SC{T}_{j}' for j in range(len(pres)))})

{shape_lemmas}

theorem shardsOK6SC{T} : ShardsOK6SC tables6SC{T} shapes7_6SC{T} := by
  intro h hh
  simp only [shapes7_6SC{T}, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with {' | '.join(['rfl'] * len(shp))}
{chr(10).join(f'  · exact shape6SC{T}_{i}' for i in range(len(shp)))}

theorem stepOK6SC{T} : StepOK6SC tables6SC{T} := check6SC_of_shards _ _ shapesCover6SC{T} shardsOK6SC{T}

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.stepOK6SC{T}
'''
    out[os.path.join(a.out_stronger, f'WindowAutomaton6SC{T}Sequence.lean')] = seq
    for p, t in out.items():
        os.makedirs(os.path.dirname(p), exist_ok=True)
        if not (os.path.exists(p) and open(p).read() == t):
            open(p, 'w').write(t)
    if a.sha256:
        dp = os.path.join(a.out_stronger, f'WindowAutomaton6SC{T}Data.lean')
        with open(a.sha256, 'w') as f:
            for p in [dp] + shard_paths:
                f.write(f'{hashlib.sha256(out[p].encode()).hexdigest()}  {os.path.basename(p)}\n')
    sizes = {}
    for p, t in out.items():
        k = 'shard' if 'Shard' in p else os.path.basename(p)
        sizes[k] = sizes.get(k, 0) + len(t.encode())
    summary['source_bytes'] = sizes
    summary['seconds'] = round(time.time() - t_start)
    sp = a.summary or os.path.join(DATA, f'auto6sc_{T}.json')
    os.makedirs(os.path.dirname(sp), exist_ok=True)
    json.dump(summary, open(sp, 'w'), indent=1)
    print(f'wrote {len(out)} modules ({sum(len(t) for t in out.values()) / 1e6:.1f} MB); summary {sp}', flush=True)


if __name__ == '__main__':
    main()
