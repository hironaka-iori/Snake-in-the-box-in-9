"""Generate the Lean keys, data, shard and sequence modules of a share-weighted six-centre automaton.

The automaton is milestone 23's k6 full product (34 canonical 7-direction shapes x 6^5 lumped
counts) with the step weight of milestones 28/31:

  step      one more direction d < 9 and count s; the transition is excluded by a k6 window of 3..7
            directions ending at the new vertex (either orientation) or by an H8 cut (the 8-direction
            step window with 6 counts, first interior vertex uncounted, reversed key form); otherwise
            P + pot(next) <= Q (120 s + share6) + pot(current) must hold, where share6 is the larger
            share level of the trailing 5-window (directions d(n+2..n+7), counts a(n+3..n+7)) in the
            two orientations, read from the share table.

Generic Lean side: work/spectral/stronger/WindowAutomaton6SDefs.lean (check6SAt, total_bound6S),
WindowAutomaton6SV2.lean (witness-driven shard check, the design of WindowAutomaton7V2),
DirectionWindowBridge6S.lean (covers), AggregateDirection6SConditional.lean (glue).

Input: a key set in the format of milestones/31-233-cost/data/keys233_best.json.gz
  plain  [dirs, lumped syms, basis, hints]            -> k6 exclusion table, Refuted keys
  h8     [dirs (8, reversed), 6 syms (reversed), hints] -> H8 tree, Refuted keys (7th centre uncounted)
  share  [dirs (6), 5 syms, level L, lb, basis, hints] -> share table field L; basis 'lean_floor'
         entries must satisfy L <= floorLevel (main's floors), the others become share keys
         (dirs, syms, L - 1): RefutedShare (winOf dirs) (boundsOf syms) 12 (L - 1)

Bellman-Ford (canonical labels, as milestone 31) for lambda = P/Q on the weights Q (120 s + share6) - P;
the potential, the exclusion masks, the H8 codes and the share rows are packed, decoded back, and every
transition of every label below 9 is re-checked in Python against the decoded tables while computing the
shard witnesses (each transition must have its inequality or an excluding window).

Outputs (identifiers carry the tag T):
  <out-core>/LocalWindowDirKeys6S<T>.lean      dirChunks6S<T>, h8Keys6S<T>, shareKeys6S<T>,
                                               AllRefuted6S<T>, AllRefutedShare6S<T>
  <out>/WindowAutomaton6S<T>Data.lean          tables6S<T>, shapes7_6S<T>, rows/chunk index, share shapes
  <out>/WindowAutomaton6S<T>Shard<i>_<t0>.lean 204 shards, one `decide +kernel` of check6SAtW per label
  <out>/WindowAutomaton6S<T>Sequence.lean      stepOK6S<T> : StepOK6S tables6S<T>
  <summary>                                    json for gen_lean_chain6s.py

  python gen_lean_automaton6s.py --set keys233_best.json.gz --tag T --lam 520/1 --bits 10 [--dry-run]
  python gen_lean_automaton6s.py --set toy.json --tag Toy --toy
  --shards all|none|i_t0,...   which shard modules to write; --stub-shards writes `sorry` stubs for the
  others (scratch builds only: a stub must never be committed).
"""
import argparse, gzip, itertools, json, os, sys, time
from fractions import Fraction as Fr
sys.dont_write_bytecode = True
import numpy as np
sys.set_int_max_str_digits(0)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '23-k6-lean', 'scripts'))
import gen_lean_automaton6 as GA   # canon, induced, is_rgs, shape_code, sym_idx, cnt_idx, rgs, shapes7

STRONGER = os.path.join(ROOT, 'work', 'spectral', 'stronger')
CORE = os.path.join(ROOT, 'work', 'final_lean')
DATA = os.path.join(HERE, '..', 'data')
ME = 'milestones/33-233-lean/scripts/gen_lean_automaton6s.py'
NC, NT = 6 ** 5, 6 ** 6
canon, induced, shape_code = GA.canon, GA.induced, GA.shape_code
FLOOR16 = [(0, 1, 2, 0, 3, 2), (0, 1, 2, 0, 3, 1), (0, 1, 2, 3, 0, 4), (0, 1, 2, 3, 1, 4)]


def pat155(t):
    return len(t) == 5 and t[0] == 4 and t[1] <= 4 and t[2] == 4 and t[3] <= 5 and t[4] == 3


def floor_level(c, t):
    """Mirror of DirectionWindowBridge6S.floorLevel."""
    if tuple(c) == (0, 1, 2, 0, 3, 2) and (pat155(t) or pat155(tuple(reversed(t)))):
        return 17
    return 16 if tuple(c) in FLOOR16 else 0


def enc(b, l):
    acc = 0
    for x in l:
        acc = acc * b + x
    return acc


def lst(c):
    return '[' + ', '.join(map(str, c)) + ']'


def tree(var, items, default, leaf=4):
    """Balanced `bif Nat.blt` lookup over sorted (key, value-expr) items."""
    if len(items) <= leaf:
        out = default
        for k, v in reversed(items):
            out = f'bif Nat.beq {var} {k} then {v} else\n  {out}'
        return out
    mid = len(items) // 2
    return (f'bif Nat.blt {var} {items[mid][0]} then\n  ({tree(var, items[:mid], default, leaf)}) else\n'
            f'  ({tree(var, items[mid:], default, leaf)})')


def ntree(codes):
    if not codes:
        return '.nil'
    mid = len(codes) // 2
    return f'(.node {ntree(codes[:mid])} {codes[mid]} {ntree(codes[mid + 1:])})'


def nib_lit(nibs):
    nibs = np.asarray(nibs, np.uint8)
    if len(nibs) % 2:
        nibs = np.append(nibs, np.uint8(0))
    v = int.from_bytes((nibs[0::2] | (nibs[1::2] << 4)).tobytes(), 'little')
    return f'0x{v:x}'


def pack(vals, bits):
    """Fields of `bits` bits, field k at bits*k."""
    v = 0
    for k, x in enumerate(vals):
        assert 0 <= x < 2 ** bits
        v |= int(x) << (bits * k)
    return v


def field(row, bits, k):
    return (row >> (bits * k)) & (2 ** bits - 1)


def load_set(path):
    d = json.load(gzip.open(path, 'rt') if path.endswith('.gz') else open(path))
    plain = sorted({(tuple(k[0]), tuple(k[1])) for k in d['plain']}, key=lambda k: (len(k[0]), k))
    for c, t in plain:
        assert GA.is_rgs(c) and 3 <= len(c) <= 7 and len(t) + 1 == len(c) and all(1 <= x <= 6 for x in t), (c, t)
    h8 = sorted({(tuple(k[0]), tuple(k[1])) for k in d['h8']}, key=lambda k: enc(9, k[0] + k[1]))
    for c, t in h8:
        assert GA.is_rgs(c) and len(c) == 8 and len(t) == 6 and all(1 <= x <= 6 for x in t), (c, t)
    share = {}
    for e in d['share']:
        c, t, L, basis = tuple(e[0]), tuple(e[1]), int(e[2]), e[4]
        assert GA.is_rgs(c) and len(c) == 6 and len(t) == 5 and all(1 <= x <= 6 for x in t) and L > 0
        assert (c, t) not in share
        share[(c, t)] = (L, basis)
    return plain, h8, share, d.get('summary', {})


class Tabs:
    """The tables as Lean reads them (decoded from the packed literals)."""

    def __init__(self, plain, h8, share, sbits):
        self.wshapes = sorted({k[0] for k in plain}, key=lambda c: (len(c), c))
        self.widx = {shape_code(c): i for i, c in enumerate(self.wshapes)}
        self.forb = {}
        for c, t in plain:
            r = self.widx[shape_code(c)]
            self.forb[(r, t[0])] = self.forb.get((r, t[0]), 0) | (1 << GA.sym_idx(t[1:]))
        self.hcodes = [enc(9, c + t) for c, t in h8]
        assert self.hcodes == sorted(self.hcodes) and len(set(self.hcodes)) == len(self.hcodes)
        self.sshapes = sorted({c for c, t in share})
        self.sidx = {shape_code(c): i for i, c in enumerate(self.sshapes)}
        self.sbits = sbits
        rows = {}
        for (c, t), (L, _) in share.items():
            rows.setdefault((self.sidx[shape_code(c)], t[0]), [0] * 6 ** 4)[GA.cnt_idx(t[1:])] = L
        self.shr = {k: pack(v, sbits) for k, v in rows.items()}
        # decoded views
        self.excl = {}
        for (r, s0), m in self.forb.items():
            c = self.wshapes[r]
            while m:
                b = m.bit_length() - 1
                m ^= 1 << b
                self.excl.setdefault(c, []).append((s0,) + GA.decode_rest(b, len(c) - 2))
        assert {(c, t) for c, ts in self.excl.items() for t in ts} == set(plain), 'mask decoding mismatch'
        self.hby = {}
        for code in self.hcodes:
            dg = []
            for _ in range(14):
                dg.append(code % 9); code //= 9
            assert code == 0
            dg = tuple(reversed(dg))
            self.hby.setdefault(dg[:8], []).append(dg[8:])
        assert {(c, t) for c, ts in self.hby.items() for t in ts} == set(h8), 'H8 decoding mismatch'
        self.sarr = {}
        for (r, t0), row in self.shr.items():
            c = self.sshapes[r]
            A = self.sarr.setdefault(c, np.zeros((6,) * 5, np.int64))
            for k in range(6 ** 4):
                A[(t0 - 1,) + tuple(np.unravel_index(k, (6,) * 4))] = field(row, sbits, k)
        for (c, t), (L, _) in share.items():
            assert self.sarr[c][tuple(x - 1 for x in t)] == L, 'share decoding mismatch'

    def win_codes(self, dirs, w, code):
        """k6 window codes over 6^6 (forward `code`, reversed `code + 1`; 0 = not excluded)."""
        F = np.zeros((6,) * 6, np.int8)
        pre = (slice(None),) * (6 - w)
        for t in self.excl.get(canon(tuple(reversed(dirs))), ()):
            F[pre + tuple(x - 1 for x in reversed(t))] = code + 1
        for t in self.excl.get(canon(dirs), ()):
            F[pre + tuple(x - 1 for x in t)] = code
        return F.ravel()

    def codes(self, X):
        """First excluding disjunct of each transition of the step window X (8 directions)."""
        arrs = [self.win_codes(X[8 - w - 1:], w, 2 * (w - 2) + 1) for w in range(2, 7)]
        H = np.zeros(NT, np.int8)
        for t in self.hby.get(canon(tuple(reversed(X))), ()):
            H[GA.cnt_idx(tuple(reversed(t)))] = 11
        arrs.append(H)
        out = np.zeros(NT, np.int8)
        for a in reversed(arrs):
            out = np.where(a != 0, a, out)
        return out

    def shares(self, X):
        """Forward and reversed share fields of the trailing 5-window, over 6^6 (t0 ignored)."""
        dd = X[2:8]
        z = np.zeros((6,) * 5, np.int64)
        fw = self.sarr.get(canon(dd), z)
        rv = self.sarr.get(canon(tuple(reversed(dd))), z).transpose(4, 3, 2, 1, 0)
        return np.tile(fw.ravel(), 6), np.tile(rv.ravel(), 6)


def bellman_ford(n, U, V, W, max_iter):
    order = np.argsort(V, kind='stable')
    Us, Vs, Ws = U[order], V[order], W[order]
    uv, starts = np.unique(Vs, return_index=True)
    pi = np.zeros(n, np.int64)
    for it in range(max_iter):
        mins = np.minimum.reduceat(pi[Us] + Ws, starts)
        upd = mins < pi[uv]
        if not upd.any():
            return pi, it
        pi[uv[upd]] = mins[upd]
    return None, max_iter


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--set', required=True)
    ap.add_argument('--tag', required=True)
    ap.add_argument('--lam', help='lambda P/Q in weight units (120 per alpha unit)')
    ap.add_argument('--bits', type=int, default=None)
    ap.add_argument('--toy', action='store_true', help='zero potential, lambda = 120/1, no shards')
    ap.add_argument('--expect-range', type=int, default=None)
    ap.add_argument('--expect-bound', type=int, default=None)
    ap.add_argument('--max-iter', type=int, default=5000)
    ap.add_argument('--chunk', type=int, default=400)
    ap.add_argument('--shards', default='all')
    ap.add_argument('--stub-shards', action='store_true')
    ap.add_argument('--out-stronger', default=STRONGER)
    ap.add_argument('--out-core', default=CORE)
    ap.add_argument('--summary', default=None)
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    T = a.tag
    t_start = time.time()
    plain, h8, share, ssum = load_set(a.set)
    for (c, t), (L, basis) in share.items():
        if basis == 'lean_floor':
            assert L <= floor_level(c, t), ('floor entry above the Lean floor', c, t, L)
    skeys = sorted((c, t, L - 1) for (c, t), (L, b) in share.items() if L > floor_level(c, t))
    sbits = max(L for L, _ in share.values()).bit_length()
    tb = Tabs(plain, h8, share, sbits)
    shp = GA.shapes7()
    s7 = {c: i for i, c in enumerate(shp)}
    assert len(shp) == 34
    for c in GA.rgs(8):
        if induced(c):
            assert c[:7] in s7 and c[7] < 9
    print(f'{len(plain)} plain keys, {len(h8)} H8 keys, {len(share)} share fields '
          f'({len(share) - len(skeys)} on Lean floors, {len(skeys)} share keys), {sbits}-bit share fields; '
          f'{len(tb.wshapes)} window shapes, {len(tb.forb)} exclusion rows, {len(tb.shr)} share rows', flush=True)

    x = np.arange(NT)
    s = x % 6 + 1
    if a.toy:
        P, Q, B, rng, iters, ntr = 120, 1, 1, 0, 0, 0
        pi = np.zeros(34 * NC, np.int64)
    else:
        lam = Fr(a.lam)
        P, Q = lam.numerator, lam.denominator
        Us, Vs, Ws = [], [], []
        for i, c in enumerate(shp):
            for d in range(min(max(c) + 2, 9)):          # canonical labels (the rest repeat them)
                X = c + (d,)
                if not induced(X):
                    continue
                j = s7[canon(X[1:])]
                ok = tb.codes(X) == 0
                fw, rv = tb.shares(X)
                w = Q * (120 * s + np.maximum(fw, rv)) - P
                Us.append(i * NC + x[ok] // 6); Vs.append(j * NC + x[ok] % NC); Ws.append(w[ok])
        U, V, W = np.concatenate(Us), np.concatenate(Vs), np.concatenate(Ws)
        del Us, Vs, Ws
        print(f'{34 * NC} states, {len(U)} allowed transitions (canonical labels); '
              f'Bellman-Ford for lambda = {P}/{Q}', flush=True)
        pi, iters = bellman_ford(34 * NC, U, V, W, a.max_iter)
        if pi is None:
            raise SystemExit(f'no potential after {iters} rounds')
        pi = pi - pi.min()
        rng = int(pi.max())
        B = a.bits or max(1, rng.bit_length())
        assert rng < 2 ** B, f'range {rng} does not fit {B} bits'
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
    # Python re-check of every transition of every label against the decoded tables: the witness
    # codes of check6SAtW (0 = inequality with the forward share, 12 = with the reversed share,
    # 1..10 = k6 window, 11 = H8)
    witness, census, ntr = {}, np.zeros(16, np.int64), 0
    for i, c in enumerate(shp):
        for d in range(9):
            X = c + (d,)
            if not induced(X):
                continue
            j = s7[canon(X[1:])]
            wc = tb.codes(X)
            fw, rv = tb.shares(X)
            src, dst = dpi[i * NC + x // 6], dpi[j * NC + x % NC]
            okf = P + dst <= Q * (120 * s + fw) + src
            okr = P + dst <= Q * (120 * s + rv) + src
            code = np.where(okf, 0, np.where(okr, 12, wc)).astype(np.int8)
            bad = ~okf & ~okr & (wc == 0)
            assert not bad.any(), ('transition without a witness', X, int(bad.sum()))
            witness[(i, d)] = code
            census += np.bincount(code, minlength=16)
            ntr += NT
    print(f'potential range {rng} ({B} bits), {iters} rounds; Python re-check passed on {ntr} transitions '
          f'(all labels); witness codes {dict((k, int(v)) for k, v in enumerate(census) if v)}', flush=True)
    R = 2 ** B - 1
    N = (1099800 * Q + 7 * P + R) // (P + 4200 * Q)
    print(f'bound: ({P} + 4200*{Q}) m <= 1099800*{Q} + 7*{P} + {R} = {1099800 * Q + 7 * P + R}, so m <= {N}',
          flush=True)
    if a.expect_range is not None:
        assert rng == a.expect_range, (rng, a.expect_range)
    if a.expect_bound is not None:
        assert N == a.expect_bound, (N, a.expect_bound)

    # chunks of whole exclusion rows for the cover
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
    summary = dict(tag=T, set=os.path.relpath(os.path.abspath(a.set), ROOT), plain_keys=len(plain),
                   h8_keys=len(h8), share_fields=len(share), share_keys=len(skeys),
                   share_on_floors=len(share) - len(skeys), sbits=sbits, P=P, Q=Q, bits=B,
                   potential_range=rng, bound=N, toy=a.toy, bf_rounds=iters, transitions_checked=ntr,
                   witness_census={str(k): int(v) for k, v in enumerate(census) if v},
                   k_chunks=len(chunks), rows=[[list(c), s0, where[(c, s0)]] for c, s0 in rowlist],
                   share_shapes=[list(c) for c in tb.sshapes], seconds=round(time.time() - t_start))
    if a.dry_run:
        print(json.dumps({k: v for k, v in summary.items() if k not in ('rows', 'share_shapes')}), flush=True)
        return
    out = {}
    nc = 'noncomputable '
    keys_mod = f'''import DirectionWindowBridge6S

/-!
# Certificate keys of the share-weighted six-centre automaton `{T}`

Generated by `{ME}` from `{summary["set"]}`.

* `dirChunks6S{T}`: {len(plain)} plain k6 keys `(dirs, lumped syms)`, chunks of whole exclusion rows;
  certificate `Refuted (winOf dirs) (boundsOf syms)`.
* `h8Keys6S{T}`: {len(h8)} H8 keys (8 directions, 6 counts, reversed: the uncounted vertex last);
  certificate `Refuted (winOf dirs) (boundsOf syms)` with 6 bounds for 7 interior vertices.
* `shareKeys6S{T}`: {len(skeys)} share thresholds `(dirs, syms, K)`; certificate
  `RefutedShare (winOf dirs) (boundsOf syms) 12 K` (share sum of the 5 centres at least `K + 1`).
  The other {len(share) - len(skeys)} share fields are covered by main's floor theorems (`Floors233`).
-/

set_option maxHeartbeats 0

namespace Snake9.LocalWindow

''' + ''.join(f'''{nc}def dirChunk6S{T}_{ci} : List (List Nat × List Nat) := [
''' + ',\n'.join(f'  ({lst(d)}, {lst(t)})' for d, t in ch) + ''']

''' for ci, ch in enumerate(chunks)) + f'''{nc}def dirChunks6S{T} : List (List (List Nat × List Nat)) :=
  [{', '.join(f'dirChunk6S{T}_{ci}' for ci in range(len(chunks)))}]

{nc}def dirKeys6S{T} : List (List Nat × List Nat) := dirChunks6S{T}.flatten

{nc}def h8Keys6S{T} : List (List Nat × List Nat) := [
''' + ',\n'.join(f'  ({lst(d)}, {lst(t)})' for d, t in h8) + f''']

{nc}def shareKeys6S{T} : List (List Nat × List Nat × Nat) := [
''' + ',\n'.join(f'  ({lst(d)}, {lst(t)}, {k})' for d, t, k in skeys) + f''']

/-- The plain and H8 certificate statements. -/
def AllRefuted6S{T} : Prop := AllRefutedList dirKeys6S{T} ∧ AllRefutedList h8Keys6S{T}

/-- The share certificate statements. -/
def AllRefutedShare6S{T} : Prop := AllRefutedShareList shareKeys6S{T}

end Snake9.LocalWindow
'''
    out[os.path.join(a.out_core, f'LocalWindowDirKeys6S{T}.lean')] = keys_mod
    witems = sorted((cd, str(i)) for cd, i in tb.widx.items())
    fitems = sorted((r * 7 + s0, f'0x{m:x}') for (r, s0), m in tb.forb.items() if m)
    pitems = sorted((shape_code(c), str(i)) for i, c in enumerate(shp))
    sitems = sorted((cd, str(i)) for cd, i in tb.sidx.items())
    if a.toy:
        potdef = f'def potMask6S{T} (_r _t0 : Nat) : Nat := 0'
    else:
        defs, sel = [], []
        for i in range(34):
            it = sorted((t0, f'0x{pots[(i, t0)]:x}') for t0 in range(1, 7) if pots[(i, t0)])
            if it:
                defs.append(f'def potRow6S{T}_{i} (t0 : Nat) : Nat :=\n  {tree("t0", it, "0")}\n')
                sel.append((i, f'potRow6S{T}_{i} t0'))
        potdef = ('\n'.join(defs) + f'\ndef potMask6S{T} (r t0 : Nat) : Nat :=\n  {tree("r", sel, "0")}')
    sdefs, ssel = [], []
    for r in range(len(tb.sshapes)):
        it = sorted((t0, f'0x{tb.shr[(r, t0)]:x}') for t0 in range(1, 7) if tb.shr.get((r, t0)))
        if it:
            sdefs.append(f'def shrRow6S{T}_{r} (t0 : Nat) : Nat :=\n  {tree("t0", it, "0")}\n')
            ssel.append((r, f'shrRow6S{T}_{r} t0'))
    shrdef = '\n'.join(sdefs) + f'\ndef shrMask6S{T} (r t0 : Nat) : Nat :=\n  {tree("r", ssel, "0")}'
    data = f'''/-
Generated by {ME}.  Do not edit by hand.
Share-weighted six-centre automaton `{T}` from `{summary["set"]}`: {len(plain)} plain keys,
{len(h8)} H8 keys, {len(share)} share fields ({sbits} bits); lambda = {P}/{Q} (weight units, 120 per
alpha unit), potential on {34 * NC} states, range {rng} ({B}-bit fields); bound m <= {N}.
-/
import WindowAutomaton6SDefs

set_option maxHeartbeats 0

namespace Snake9.WindowAutomaton

/-- Canonical window shapes (3 to 7 directions) ↦ exclusion row. -/
def wIdx6S{T} (c : Nat) : Nat :=
  {tree("c", witems, str(len(tb.wshapes)))}

/-- Exclusion rows: `7 * row + first count` ↦ mask over `symIdx` of the other counts. -/
def forbRows6S{T} (k : Nat) : Nat :=
  {tree("k", fitems, "0")}

def forbMask6S{T} (r s : Nat) : Nat := forbRows6S{T} (r * 7 + s)

/-- Canonical induced 7-direction shapes ↦ potential row. -/
def pIdx6S{T} (c : Nat) : Nat :=
  {tree("c", pitems, "34")}

/-- Potential rows: (7-shape, first count) ↦ {B}-bit fields at `cntIdx6` of the other four. -/
{potdef}

/-- 6-direction share shapes ↦ share row. -/
def sIdx6S{T} (c : Nat) : Nat :=
  {tree("c", sitems, str(len(tb.sshapes)))}

/-- Share rows: (share shape, first count) ↦ {sbits}-bit fields at `cntIdx6` of the other four. -/
{shrdef}

/-- The H8 keys: `encB 9 (dirs ++ syms) 0`, in order. -/
def h8Tree6S{T} : NTree :=
  {ntree(tb.hcodes)}

def tables6{T}k6 : Tables6 where
  wIdx := wIdx6S{T}
  forb := forbMask6S{T}
  pIdx := pIdx6S{T}
  pot := potMask6S{T}
  bits := {B}
  num := {P}
  den := {Q}

def tables6S{T} : Tables6S where
  k6 := tables6{T}k6
  htree := h8Tree6S{T}
  sIdx := sIdx6S{T}
  shr := shrMask6S{T}
  sbits := {sbits}

def shapes7_6S{T} : List (List Nat) := [{', '.join(lst(c) for c in shp)}]

/-- The nonzero exclusion rows (window shape, first count), for `cover6_chunks`. -/
def rows6S{T} : List (List Nat × Nat) := [{', '.join(f'({lst(c)}, {s0})' for c, s0 in rowlist)}]

/-- The share shapes with a nonzero row, for `shareCover_rows`. -/
def sshapes6S{T} : List (List Nat) := [{', '.join(lst(c) for c in tb.sshapes)}]

end Snake9.WindowAutomaton
'''
    out[os.path.join(a.out_stronger, f'WindowAutomaton6S{T}Data.lean')] = data
    if a.toy:
        seq = f'''/-
Generated by {ME} (--toy): the step test of `tables6S{T}` holds trivially
(zero potential, lambda = 120/1), so no shards are needed.
-/
import WindowAutomaton6S{T}Data

namespace Snake9.WindowAutomaton

theorem stepOK6S{T} : StepOK6S tables6S{T} := stepOK6S_of_trivial _ (fun _ _ => rfl) (by decide)

end Snake9.WindowAutomaton
'''
    else:
        want = None if a.shards == 'all' else (set() if a.shards == 'none' else
                                                {tuple(map(int, q.split('_'))) for q in a.shards.split(',')})
        for i, c in enumerate(shp):
            for t0 in range(1, 7):
                p = os.path.join(a.out_stronger, f'WindowAutomaton6S{T}Shard{i}_{t0}.lean')
                head = f'''/-
Generated by {ME}.  Shard ({i}, {t0}) of the step table of `tables6S{T}`:
canonical 7-shape {lst(c)} extended by every label below 9, first count {t0}.'''
                stmt = f'allBelow 9 (fun d => check6SAt tables6S{T} ({lst(c)} ++ [d]) {t0}) = true'
                if want is not None and (i, t0) not in want:
                    if a.stub_shards:
                        out[p] = f'''{head}
STUB (scratch build only, never commit): the statement is assumed.
-/
import WindowAutomaton6S{T}Data

namespace Snake9.WindowAutomaton

theorem shard6S{T}_{i}_{t0} : {stmt} := sorry

end Snake9.WindowAutomaton
'''
                    continue
                decls = []
                for d in range(9):
                    X = c + (d,)
                    nm = f'shard6S{T}_{i}_{t0}_{d}'
                    cc = f'({lst(c)} ++ [{d}])'
                    if induced(X):
                        code = witness[(i, d)][(t0 - 1) * NC:t0 * NC]
                        decls.append(f'''set_option maxRecDepth 100000 in
theorem {nm}_w : check6SAtW tables6S{T} {cc} {t0}
    (nat_lit {nib_lit(code)}) = true := by
  decide +kernel

theorem {nm} : check6SAt tables6S{T} {cc} {t0} = true := check6SAt_of_W _ _ _ _ {nm}_w
''')
                    else:
                        decls.append(f'''theorem {nm} : check6SAt tables6S{T} {cc} {t0} = true := by
  decide +kernel -- not induced: no transition
''')
                out[p] = f'''{head}
One witness-driven kernel check (`check6SAtW`, WindowAutomaton6SV2) per label: a 4-bit code per
transition chooses the disjunct the kernel evaluates; `check6SAt_of_W` gives `check6SAt` whatever
the codes.
-/
import WindowAutomaton6S{T}Data
import WindowAutomaton6SV2

set_option Elab.async false

namespace Snake9.WindowAutomaton

{chr(10).join(decls)}
theorem shard6S{T}_{i}_{t0} : {stmt} :=
  allBelow9_of _ {' '.join(f'shard6S{T}_{i}_{t0}_{d}' for d in range(9))}

end Snake9.WindowAutomaton
'''
        imports = '\n'.join(f'import WindowAutomaton6S{T}Shard{i}_{t0}' for i in range(34) for t0 in range(1, 7))
        shape_lemmas = '\n\n'.join(f'''theorem shape6S{T}_{i} : ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    allBelow 9 (fun d => check6SAt tables6S{T} ({lst(c)} ++ [d]) t0) = true := by
  intro t0 h1 h6
  have : t0 = 1 ∨ t0 = 2 ∨ t0 = 3 ∨ t0 = 4 ∨ t0 = 5 ∨ t0 = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
{chr(10).join(f'  · exact shard6S{T}_{i}_{t0}' for t0 in range(1, 7))}''' for i, c in enumerate(shp))
        pres = GA.rgs(5)
        pre_lemmas = '\n\n'.join(f'''set_option maxRecDepth 100000 in
theorem shapesPre6S{T}_{j} :
    allRGS 3 (rgsBound {lst(q)} 0) (fun l => shapeTest6 shapes7_6S{T} ({lst(q)} ++ l)) = true := by
  decide +kernel''' for j, q in enumerate(pres))
        seq = f'''/-
Generated by {ME}.
Combines the {6 * len(shp)} shards of `tables6S{T}` into `StepOK6S tables6S{T}`.
-/
{imports}

set_option Elab.async false

namespace Snake9.WindowAutomaton

{pre_lemmas}

theorem shapesCover6S{T} : ShapesCover shapes7_6S{T} = true :=
  shapesCover_of _ [{', '.join(lst(q) for q in pres)}] 5 3 rfl (by decide +kernel) (by
    intro pre h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with {' | '.join(['rfl'] * len(pres))}
{chr(10).join(f'    · exact shapesPre6S{T}_{j}' for j in range(len(pres)))})

{shape_lemmas}

theorem shardsOK6S{T} : ShardsOK6S tables6S{T} shapes7_6S{T} := by
  intro h hh
  simp only [shapes7_6S{T}, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with {' | '.join(['rfl'] * len(shp))}
{chr(10).join(f'  · exact shape6S{T}_{i}' for i in range(len(shp)))}

theorem stepOK6S{T} : StepOK6S tables6S{T} := check6S_of_shards _ _ shapesCover6S{T} shardsOK6S{T}

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.stepOK6S{T}
'''
    out[os.path.join(a.out_stronger, f'WindowAutomaton6S{T}Sequence.lean')] = seq
    for p, t in out.items():
        os.makedirs(os.path.dirname(p), exist_ok=True)
        if not (os.path.exists(p) and open(p).read() == t):
            open(p, 'w').write(t)
    sp = a.summary or os.path.join(DATA, f'auto6s_{T}.json')
    os.makedirs(os.path.dirname(sp), exist_ok=True)
    json.dump(summary, open(sp, 'w'), indent=1)
    print(f'wrote {len(out)} modules ({sum(len(t) for t in out.values()) / 1e6:.1f} MB); summary {sp}', flush=True)


if __name__ == '__main__':
    main()
