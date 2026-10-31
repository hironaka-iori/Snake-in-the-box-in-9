"""Generate the Lean keys, data, shard and sequence modules of a seven-centre (k = 7) automaton.

Seven-centre version of `milestones/23-k6-lean/scripts/gen_lean_automaton6.py` for the generic
Lean framework `work/spectral/stronger/WindowAutomaton7Defs.lean` (milestones/25-k7-234):

  states    canonical induced 8-direction shape (132 of them) x 6 lumped counts a2..a7 (6^6),
            6,158,592 in all;
  step      label d8 (a restricted growth label of the shape) and count s = a8; the step window
            X = shape ++ [d8] (505 induced ones) is tested by
              (own)  the closed-set skip: the source state's own k6 windows (3..7 directions
                     ending at its last vertex) are excluded -> nothing to check;
              (k6)   windows of 3..7 directions ending at the new vertex, both orientations;
              (F8)   the 8-direction window X[1:] with the 7 counts a2..a8, both orientations;
              (H9)   the 9-direction window X with the counts a2..a8, key (canon(rev X), rev counts);
            otherwise P + pot(next) <= Q s + pot(cur) must hold.
  bound     (P + 35 Q) m + 7 Q <= 9171 Q + 8 P + 2^B - 1.

Lean tables (`Tables7`):
  * k6/F8 exclusion masks keyed by (window shape, first count), bits at `symIdx` of the rest;
  * H9 keys as a balanced search tree (`NTree`) of `encB 9 (dirs ++ syms) 0`, in key order;
  * potential rows keyed by (8-shape, t0, t1), `B`-bit fields at `cntIdx6 [t2..t5]`;
  * every lookup is a balanced `bif Nat.blt` tree, so a lookup costs O(log rows).

The potential is computed by Gauss-Seidel Bellman-Ford on the full product (dead sources
skipped) for lambda = P/Q; the emitted tables are decoded back (masks -> keys, tree -> codes,
rows -> potential) and every transition of the full product is re-checked against the decoded
potential before anything is written.

Outputs (identifiers carry the tag T):
  <core>/LocalWindowDirKeys7<T>.lean          `dirChunks7<T>`, `dirKeys7<T>`, `hKeys7<T>`, `AllRefuted7<T>`
  <core>/LocalWindowDirKeys7<T>_P<j>.lean     the key chunks (at most --keys-per-module keys each)
  <stronger>/WindowAutomaton7<T>Data.lean     `tables7<T> : Tables7`, `shapes8_7<T>`, `rows7<T>`
  <stronger>/WindowAutomaton7<T>Shard<i>_<t0>.lean   132 x 6 = 792 shards; one `decide +kernel`
        per (label, t1, t2): `check7In2 tables7<T> (shape ++ [d]) t0 t1 t2 = true` (6^4 transitions;
        --split t1: per (label, t1), 6^5 transitions, about 4x the kernel memory)
  <stronger>/WindowAutomaton7<T>Sequence.lean `stepOK7<T> : StepOK7 tables7<T>`
  <summary>                                    JSON for gen_lean_chain7.py

  python gen_lean_automaton7.py --keys data/keys_l417d.json.gz --tag L417d --lam 4516/1083 \
      --out-stronger DIR --out-core DIR
  python gen_lean_automaton7.py --keys data/keys_best234.json.gz --tag B234 --lam 6423/1544 \
      --noncomputable --shards none
  python gen_lean_automaton7.py --keys lean/data/toy_keys7.json --tag Toy --toy

Key files: {"keys": [[kind, dirs, syms], ...]} with kind "k6" (3..7 directions, one count fewer),
"F" (8 directions, 7 counts) or "H" (9 directions, 7 counts, reversed uncounted-last form);
counts are lumped symbols 1..6.
"""
import argparse, gzip, json, os, sys, time
from fractions import Fraction as Fr
import numpy as np
sys.set_int_max_str_digits(0)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
STRONGER = os.path.join(ROOT, 'work', 'spectral', 'stronger')
CORE = os.path.join(ROOT, 'work', 'final_lean')
DATA = os.path.join(HERE, '..', 'data')
ME = 'milestones/25-k7-234/lean/scripts/gen_lean_automaton7.py'
NS = 6 ** 6          # count states per 8-shape
N7 = 6 ** 7          # (state counts, new count)


def canon(ds):
    m, r = {}, []
    for d in ds:
        m.setdefault(d, len(m)); r.append(m[d])
    return tuple(r)


def induced(ds):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ (1 << d))
    return len(set(vs)) == len(vs) and all(bin(vs[i] ^ vs[j]).count('1') != 1
                                           for i in range(len(vs)) for j in range(i + 2, len(vs)))


def is_rgs(l):
    m = 0
    for a in l:
        if a > m:
            return False
        m = max(m, a + 1)
    return True


def rgs_bound(l):
    m = 0
    for a in l:
        m = max(m, a + 1)
    return m


def rgs(n):
    out = []

    def go(m, l):
        if len(l) == n:
            out.append(tuple(l)); return
        for a in range(m + 1):
            go(max(m, a + 1), l + [a])
    go(0, [])
    return out


def shape_code(l):
    acc = 1
    for a in l:
        acc = acc * 8 + a
    return acc


def enc(b, l):
    acc = 0
    for a in l:
        acc = acc * b + a
    return acc


def cidx(t):
    return enc(6, [s - 1 for s in t])


def lst(c):
    return '[' + ', '.join(map(str, c)) + ']'


# ------------------------------------------------------------------ keys
def load_keys(paths):
    k6, hk = set(), set()
    for path in paths:
        op = gzip.open if path.endswith('.gz') else open
        d = json.load(op(path, 'rt'))
        for kind, dirs, syms in d['keys']:
            dirs, syms = tuple(dirs), tuple(syms)
            assert is_rgs(dirs) and all(1 <= s <= 6 for s in syms), (kind, dirs, syms)
            if kind == 'H':
                assert len(dirs) == 9 and len(syms) == 7, (kind, dirs, syms)
                hk.add((dirs, syms))
            else:
                assert kind in ('k6', 'F') and 3 <= len(dirs) <= 8 and len(syms) + 1 == len(dirs), \
                    (kind, dirs, syms)
                k6.add((dirs, syms))
    k6 = sorted(k6, key=lambda k: (len(k[0]), k))
    hk = sorted(hk, key=lambda k: enc(9, k[0] + k[1]))
    return k6, hk


def build_tables(k6):
    wshapes = sorted({k[0] for k in k6}, key=lambda c: (len(c), c))
    widx = {shape_code(c): i for i, c in enumerate(wshapes)}
    assert len(widx) == len(wshapes)
    forb = {}
    for dirs, syms in k6:
        r = widx[shape_code(dirs)]
        forb[(r, syms[0])] = forb.get((r, syms[0]), 0) | (1 << enc(7, syms[1:]))
    return wshapes, widx, forb


def decode_rest(b, n):
    out = []
    for _ in range(n):
        out.append(b % 7); b //= 7
    assert b == 0
    return tuple(reversed(out))


# ------------------------------------------------------------------ product
class Product:
    """The full k7 product, with exclusions computed from the decoded tables."""

    def __init__(self, excl, hset):
        # excl: canonical dirs -> set of syms (decoded k6/F8 masks); hset: set of (dirs, syms)
        self.excl, self.hset = excl, hset
        self.hby = {}
        for ds, sy in hset:
            self.hby.setdefault(ds, []).append(sy)
        self.shapes = [c for c in rgs(8) if induced(c)]
        assert len(self.shapes) == 132
        self.sidx = {c: i for i, c in enumerate(self.shapes)}
        self.X = []
        for i, h in enumerate(self.shapes):
            for d in range(rgs_bound(h) + 1):
                X = h + (d,)
                if induced(X):
                    self.X.append((i, d, self.sidx[canon(X[1:])], X))
        assert len(self.X) == 505

    def win(self, F, dirs, w, n):
        """Mark in F (n counts) the tuples whose last w counts are excluded on `dirs`."""
        pre = (slice(None),) * (n - w)
        for sy in self.excl.get(canon(dirs), ()):
            F[pre + tuple(x - 1 for x in sy)] = True
        for sy in self.excl.get(canon(tuple(reversed(dirs))), ()):
            F[pre + tuple(x - 1 for x in reversed(sy))] = True

    def live(self, h):
        F = np.zeros((6,) * 6, bool)
        for w in range(2, 7):
            self.win(F, h[-(w + 1):], w, 6)
        return ~F.ravel()

    def allowed(self, X, live_src):
        F = np.zeros((6,) * 7, bool)
        for w in range(2, 8):                       # k6 windows (w <= 6) and F8 (w = 7)
            self.win(F, X[-(w + 1):], w, 7)
        for sy in self.hby.get(canon(tuple(reversed(X))), ()):
            F[tuple(x - 1 for x in reversed(sy))] = True
        return (live_src.reshape(NS, 1) & ~F.reshape(NS, 6)).ravel()


def bellman_ford(Pr, masks, P, Q, max_iter):
    pi = np.zeros((132, NS), np.int64)
    w = Q * np.arange(1, 7, dtype=np.int64) - P
    BIG = np.int64(1) << 50
    dirty = np.ones(132, bool)
    for it in range(max_iter):
        nd = np.zeros(132, bool)
        for xi, (i, d, j, X) in enumerate(Pr.X):
            if not dirty[i]:
                continue
            m = masks[xi].reshape(6, NS // 6, 6)
            cand = np.where(m, pi[i].reshape(6, NS // 6, 1) + w, BIG).min(0)
            tgt = pi[j].reshape(NS // 6, 6)
            upd = cand < tgt
            if upd.any():
                tgt[upd] = cand[upd]
                nd[j] = True
        dirty = nd
        if not nd.any():
            return pi, it
    return None, max_iter


def recheck(Pr, masks, pot, P, Q):
    """Every allowed transition satisfies P + pot(v) <= Q s + pot(u); returns the count."""
    n = 0
    s = np.arange(1, 7, dtype=np.int64)
    for xi, (i, d, j, X) in enumerate(Pr.X):
        m = masks[xi].reshape(6, NS // 6, 6)
        lhs = P + pot[j].reshape(1, NS // 6, 6)
        rhs = Q * s + pot[i].reshape(6, NS // 6, 1)
        assert not (m & (lhs > rhs)).any(), ('step inequality fails', X)
        n += int(m.sum())
    return n


# ------------------------------------------------------------------ Lean emission
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


def pack_rows(pot, B):
    """(i, t0, t1) -> int with B-bit fields at cnt_idx(t2..t5)."""
    rows = {}
    shifts = np.arange(B, dtype=np.int64)
    for i in range(132):
        for t0 in range(1, 7):
            for t1 in range(1, 7):
                base = (t0 - 1) * 6 ** 5 + (t1 - 1) * 6 ** 4
                v = pot[i, base:base + 6 ** 4]
                bits = ((v[:, None] >> shifts) & 1).astype(np.uint8).ravel()
                rows[(i, t0, t1)] = int.from_bytes(np.packbits(bits, bitorder='little').tobytes(), 'little')
    return rows


def unpack_rows(rows, B):
    pot = np.zeros((132, NS), np.int64)
    for (i, t0, t1), r in rows.items():
        base = (t0 - 1) * 6 ** 5 + (t1 - 1) * 6 ** 4
        by = np.frombuffer(r.to_bytes((6 ** 4 * B + 7) // 8, 'little'), np.uint8)
        bits = np.unpackbits(by, bitorder='little')[:6 ** 4 * B].reshape(6 ** 4, B).astype(np.int64)
        pot[i, base:base + 6 ** 4] = (bits << np.arange(B, dtype=np.int64)).sum(1)
    return pot


def chunk_rows(k6, cap):
    """Chunks of whole exclusion rows (dirs, first count), at most `cap` keys unless one row
    is larger; returns the chunks and the chunk index of each row."""
    rows = {}
    for k in k6:
        rows.setdefault((k[0], k[1][0]), []).append(k)
    chunks, where = [], {}
    cur = []
    for r in sorted(rows, key=lambda r: (len(r[0]), r)):
        ks = rows[r]
        if cur and len(cur) + len(ks) > cap:
            chunks.append(cur); cur = []
        where[r] = len(chunks)
        cur = cur + ks
    if cur or not chunks:
        chunks.append(cur)
    return chunks, where


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--keys', nargs='+', required=True)
    ap.add_argument('--tag', required=True)
    ap.add_argument('--lam', help='lambda P/Q (required unless --toy)')
    ap.add_argument('--bits', type=int, default=None, help='field width (default: from the range)')
    ap.add_argument('--toy', action='store_true')
    ap.add_argument('--provisional', action='store_true', help='keys are solver answers, not certificates')
    ap.add_argument('--max-iter', type=int, default=5000)
    ap.add_argument('--chunk', type=int, default=400)
    ap.add_argument('--keys-per-module', type=int, default=4000)
    ap.add_argument('--split', choices=['t1', 't2'], default='t2',
                    help='one kernel declaration per (label, t1) [6^5 transitions, about 3 GB] '
                         'or per (label, t1, t2) [6^4 transitions, about 0.7 GB; default]')
    ap.add_argument('--out-stronger', default=STRONGER)
    ap.add_argument('--out-core', default=CORE)
    ap.add_argument('--summary', default=None)
    ap.add_argument('--shards', default='all', help="'all', 'none' or a list i_t0,i_t0,...")
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--write', choices=['all', 'shards'], default='all',
                    help="'shards': write only the shard modules selected by --shards (the summary "
                         "is still written)")
    ap.add_argument('--noncomputable', action='store_true',
                    help='write the key lists of LocalWindowDirKeys7<T> as `noncomputable def` (same '
                         'values; the kernel checks only unfold them, and the .olean is about 15 times '
                         'smaller)')
    a = ap.parse_args()
    T = a.tag
    t_start = time.time()
    k6, hk = load_keys(a.keys)
    wshapes, widx, forb = build_tables(k6)
    nrows = len(wshapes)
    # decode the masks back to keys
    excl, dec = {}, set()
    for (r, s0), m in forb.items():
        c = wshapes[r]
        while m:
            b = m.bit_length() - 1
            m ^= 1 << b
            sy = (s0,) + decode_rest(b, len(c) - 2)
            dec.add((c, sy)); excl.setdefault(c, set()).add(sy)
    assert dec == set(k6), 'mask decoding mismatch'
    hcodes = [enc(9, d + s) for d, s in hk]
    assert hcodes == sorted(hcodes) and len(set(hcodes)) == len(hcodes)
    # decode the tree codes back to keys
    hdec = set()
    for c in hcodes:
        dg = []
        for _ in range(16):
            dg.append(c % 9); c //= 9
        assert c == 0
        dg = tuple(reversed(dg))
        hdec.add((dg[:9], dg[9:]))
    assert hdec == set(hk), 'H9 decoding mismatch'
    Pr = Product(excl, hdec)
    shp = Pr.shapes
    for c in rgs(9):
        if induced(c):
            assert c[:8] in Pr.sidx
    pidx = {shape_code(c): i for i, c in enumerate(shp)}
    assert len(pidx) == 132
    print(f'{len(k6)} k6/F8 keys ({sum(len(k[0]) == 8 for k in k6)} F8), {len(hk)} H9 keys, '
          f'{nrows} window shapes, {len(forb)} exclusion rows', flush=True)

    live = [Pr.live(h) for h in shp]
    n_live = int(sum(l.sum() for l in live))
    if a.toy:
        P, Q, B, rng, iters, ntr = 1, 1, 1, 0, 0, 0
        rows = {}
    else:
        lam = Fr(a.lam)
        P, Q = lam.numerator, lam.denominator
        masks = [Pr.allowed(X, live[i]) for (i, d, j, X) in Pr.X]
        print(f'{n_live} live states of {132 * NS}; {sum(int(m.sum()) for m in masks)} allowed '
              f'transitions; Bellman-Ford for lambda = {P}/{Q}', flush=True)
        pi, iters = bellman_ford(Pr, masks, P, Q, a.max_iter)
        if pi is None:
            raise SystemExit(f'no potential after {iters} rounds: lambda {P}/{Q} is above the '
                             f'minimum cycle mean of the full product (or raise --max-iter)')
        pi = pi - pi.min()
        rng = int(pi.max())
        B = a.bits or max(1, rng.bit_length())
        assert rng < 2 ** B
        rows = pack_rows(pi, B)
        dpi = unpack_rows(rows, B)
        assert (dpi == pi).all()
        ntr = recheck(Pr, masks, dpi, P, Q)
        print(f'potential range {rng} ({B} bits), {iters} rounds; Python re-check passed on '
              f'{ntr} transitions', flush=True)
        del masks
    C = (2 ** B - 1) + 8 * P - 7 * Q
    N = (9171 * Q + 8 * P + 2 ** B - 1 - 7 * Q) // (P + 35 * Q)
    chunks, where = chunk_rows(k6, a.chunk)
    hchunks = [hk[i:i + a.chunk] for i in range(0, len(hk), a.chunk)]
    rowlist = sorted(forb, key=lambda r: (len(wshapes[r[0]]), wshapes[r[0]], r[1]))
    summary = dict(tag=T, k6_keys=len(k6), F8=sum(len(k[0]) == 8 for k in k6), H9=len(hk), P=P, Q=Q,
                   bits=B, potential_range=rng, bound=N, toy=a.toy, provisional=a.provisional,
                   bf_rounds=iters, live_states=n_live, checked_transitions=ntr,
                   window_shapes=nrows, exclusion_rows=len(forb),
                   sources=[os.path.relpath(os.path.abspath(p), ROOT) for p in a.keys],
                   seconds=round(time.time() - t_start),
                   rows=[[list(wshapes[r]), s0, where[(wshapes[r], s0)]] for r, s0 in rowlist])
    print(json.dumps({k: v for k, v in summary.items() if k != 'rows'}), flush=True)
    if a.dry_run:
        return
    src = ', '.join(summary['sources']) + (' (PROVISIONAL: solver answers, not certificates)'
                                           if a.provisional else '')

    nc = 'noncomputable ' if a.noncomputable else ''

    def chunk_defs(name, chs, start=0):
        return ''.join(f'{nc}def {name}_{start + ci} : List (List Nat × List Nat) := [\n'
                       + ',\n'.join(f'  ({lst(d)}, {lst(s)})' for d, s in ch) + ']\n\n'
                       for ci, ch in enumerate(chs))
    # The chunk definitions go into part modules of at most --keys-per-module keys: the
    # elaborator keeps every definition of a module in memory (about 1 GB per 7,000 keys).
    allch = [('dirKeys7' + T, ci, ch) for ci, ch in enumerate(chunks)] + \
            [('hKeys7' + T, ci, ch) for ci, ch in enumerate(hchunks)]
    parts, cur, n = [], [], 0
    for e in allch:
        if cur and n + len(e[2]) > a.keys_per_module:
            parts.append(cur); cur, n = [], 0
        cur.append(e); n += len(e[2])
    parts.append(cur)
    part_mods = {}
    for pi, part in enumerate(parts):
        part_mods[f'LocalWindowDirKeys7{T}_P{pi}'] = (f'''import LocalWindowDirModel

/-! Part {pi} of the window keys of the seven-centre automaton `{T}` (generated by `{ME}`). -/

set_option maxHeartbeats 0

namespace Snake9.LocalWindow

''' + ''.join(chunk_defs(nm, [ch], ci) for nm, ci, ch in part) + 'end Snake9.LocalWindow\n')
    keys_mod = '\n'.join(f'import {m}' for m in part_mods) + f'''

/-!
# Window keys of the seven-centre automaton `{T}`

Generated by `{ME}` from {src}.
* `dirKeys7{T}`: {len(k6)} k6/F8 keys (canonical direction list of 3 to 8 directions, one
  lumped count per interior vertex), in chunks of whole exclusion rows (`dirChunks7{T}`, used
  by the row-by-row cover).
* `hKeys7{T}`: {len(hk)} H9 keys (9 directions, 7 counts, in the reversed form whose last
  interior vertex is uncounted), ordered by `encB 9 (dirs ++ syms) 0`.
Every key's certificate is `Refuted (winOf ds) (boundsOf syms)`.  The chunks are defined in
the part modules `LocalWindowDirKeys7{T}_P<i>`.
-/

namespace Snake9.LocalWindow

{nc}def dirChunks7{T} : List (List (List Nat × List Nat)) :=
  [{', '.join(f'dirKeys7{T}_{ci}' for ci in range(len(chunks)))}]

{nc}def dirKeys7{T} : List (List Nat × List Nat) := dirChunks7{T}.flatten

{nc}def hChunks7{T} : List (List (List Nat × List Nat)) :=
  [{', '.join(f'hKeys7{T}_{ci}' for ci in range(len(hchunks)))}]

{nc}def hKeys7{T} : List (List Nat × List Nat) := hChunks7{T}.flatten

/-- The certificate statements of the seven-centre automaton `{T}`. -/
def AllRefuted7{T} : Prop := AllRefutedList dirKeys7{T} ∧ AllRefutedList hKeys7{T}

end Snake9.LocalWindow
'''
    hcc = [[enc(9, d + s) for d, s in ch] for ch in hchunks]
    hsubs = ''.join(f'def hSub7{T}_{ci} : NTree :=\n  {ntree(hc[:-1])}\n\n' for ci, hc in enumerate(hcc))
    summary['k_chunks'] = len(chunks)
    summary['h_chunks'] = len(hchunks)
    witems = sorted((c, str(i)) for c, i in widx.items())
    fitems = sorted((r * 7 + s, f'0x{m:x}') for (r, s), m in forb.items() if m)
    pitems = sorted((c, str(i)) for c, i in pidx.items())
    if a.toy:
        potdef = f'def potMask7{T} (_r _t0 _t1 : Nat) : Nat := 0'
    else:
        # one definition per 8-shape (36 rows each): a single definition with all 4,752
        # rows times out in the elaborator
        defs, sel = [], []
        for i in range(132):
            it = sorted((t0 * 7 + t1, f'0x{r:x}') for (j, t0, t1), r in rows.items() if j == i and r)
            if it:
                defs.append(f'def potRow7{T}_{i} (k : Nat) : Nat :=\n  {tree("k", it, "0")}\n')
                sel.append((i, f'potRow7{T}_{i} k'))
        potdef = ('\n'.join(defs) + f'\n/-- Shape row ↦ its potential rows, `7 * t0 + t1` ↦ row. -/\n'
                  f'def potSel7{T} (r k : Nat) : Nat :=\n  {tree("r", sel, "0")}\n\n'
                  f'def potMask7{T} (r t0 t1 : Nat) : Nat := potSel7{T} r (t0 * 7 + t1)')
    data = f'''/-
Generated by {ME}.  Do not edit by hand.
Seven-centre automaton `{T}`: {len(k6)} k6/F8 keys and {len(hk)} H9 keys ({src}),
lambda = {P}/{Q}, potential on {132 * NS} states ({n_live} live), range {rng} ({B}-bit fields).
-/
import WindowAutomaton7Defs

set_option maxHeartbeats 0

namespace Snake9.WindowAutomaton

/-- Canonical window shapes (3 to 8 directions) ↦ exclusion row. -/
def wIdx7{T} (c : Nat) : Nat :=
  {tree("c", witems, str(nrows))}

/-- Exclusion rows: `7 * row + first count` ↦ mask over `symIdx` of the other counts. -/
def forbRows7{T} (k : Nat) : Nat :=
  {tree("k", fitems, "0")}

def forbMask7{T} (r s : Nat) : Nat := forbRows7{T} (r * 7 + s)

/-- Canonical induced 8-direction shapes ↦ potential row. -/
def pIdx7{T} (c : Nat) : Nat :=
  {tree("c", pitems, "132")}

/-- Potential rows: `49 * shape + 7 * t0 + t1` ↦ {B}-bit fields at `cntIdx6 [t2, t3, t4, t5]`. -/
{potdef}

{hsubs}/-- The H9 keys: `encB 9 (dirs ++ syms) 0`, in order, one balanced subtree per key chunk
(the last code of a chunk is its spine node), so that `coverH_spine` checks chunk by chunk. -/
def hPieces7{T} : List (NTree × Nat) := [{', '.join(f'(hSub7{T}_{ci}, {hc[-1]})' for ci, hc in enumerate(hcc))}]

def hTree7{T} : NTree := NTree.spine hPieces7{T}

def tables7{T} : Tables7 where
  wIdx := wIdx7{T}
  forb := forbMask7{T}
  pIdx := pIdx7{T}
  pot := potMask7{T}
  htree := hTree7{T}
  bits := {B}
  num := {P}
  den := {Q}

def shapes8_7{T} : List (List Nat) := [{', '.join(lst(c) for c in shp)}]

/-- The nonzero exclusion rows (window shape, first count), for `cover7_rows`. -/
def rows7{T} : List (List Nat × Nat) := [{', '.join(f'({lst(wshapes[r])}, {s0})' for r, s0 in rowlist)}]

end Snake9.WindowAutomaton
'''
    out = {os.path.join(a.out_core, f'{m}.lean'): t for m, t in part_mods.items()}
    out |= {os.path.join(a.out_core, f'LocalWindowDirKeys7{T}.lean'): keys_mod,
           os.path.join(a.out_stronger, f'WindowAutomaton7{T}Data.lean'): data}
    if a.toy:
        seq = f'''/-
Generated by {ME} (--toy): the step test of `tables7{T}` holds trivially
(zero potential, lambda = 1), so no shards are needed.
-/
import WindowAutomaton7{T}Data

namespace Snake9.WindowAutomaton

theorem stepOK7{T} : StepOK7 tables7{T} := stepOK7_of_trivial _ (fun _ _ _ => rfl) (by decide)

end Snake9.WindowAutomaton
'''
    else:
        want = None if a.shards == 'all' else (set() if a.shards == 'none' else
                                                {tuple(map(int, x.split('_'))) for x in a.shards.split(',')})
        for i, h in enumerate(shp):
            bnd = rgs_bound(h)
            for t0 in range(1, 7):
                if want is not None and (i, t0) not in want:
                    continue
                decls, labs = [], []
                for d in range(bnd + 1):
                    c = f'({lst(h)} ++ [{d}])'
                    nm = f'shard7{T}_{i}_{t0}_{d}'
                    if induced(h + (d,)) and a.split == 't1':
                        for t1 in range(1, 7):
                            decls.append(f'''set_option maxRecDepth 100000 in
theorem {nm}_{t1} : check7In tables7{T} {c} {t0} {t1} = true := by
  decide +kernel
''')
                        decls.append(f'''theorem {nm} : check7At tables7{T} {c} {t0} = true :=
  check7At_of _ _ _ {' '.join(f'{nm}_{t1}' for t1 in range(1, 7))}
''')
                    elif induced(h + (d,)):
                        for t1 in range(1, 7):
                            for t2 in range(1, 7):
                                decls.append(f'''set_option maxRecDepth 100000 in
theorem {nm}_{t1}_{t2} : check7In2 tables7{T} {c} {t0} {t1} {t2} = true := by
  decide +kernel
''')
                            decls.append(f'''theorem {nm}_{t1} : check7In tables7{T} {c} {t0} {t1} = true :=
  check7In_of _ _ _ _ {' '.join(f'{nm}_{t1}_{t2}' for t2 in range(1, 7))}
''')
                        decls.append(f'''theorem {nm} : check7At tables7{T} {c} {t0} = true :=
  check7At_of _ _ _ {' '.join(f'{nm}_{t1}' for t1 in range(1, 7))}
''')
                    else:
                        decls.append(f'''theorem {nm} : check7At tables7{T} {c} {t0} = true := by
  decide +kernel -- not induced: no transition
''')
                    labs.append(nm)
                proof = 'rfl'
                for d, nm in enumerate(labs):
                    proof = f'allBelow_succ_of {d} _ ({proof}) {nm}'
                out[os.path.join(a.out_stronger, f'WindowAutomaton7{T}Shard{i}_{t0}.lean')] = f'''/-
Generated by {ME}.  Shard ({i}, {t0}) of the step table of `tables7{T}`:
canonical 8-shape {lst(h)} extended by every restricted growth label (at most {bnd}),
first count {t0}.  One kernel check per {'(label, t1), 6^5' if a.split == 't1' else '(label, t1, t2), 6^4'} transitions each: the kernel
caches live for one declaration, so the peak memory is that of one declaration.
-/
import WindowAutomaton7{T}Data

set_option Elab.async false

namespace Snake9.WindowAutomaton

{chr(10).join(decls)}
theorem shard7{T}_{i}_{t0} :
    allBelow {bnd + 1} (fun d => check7At tables7{T} ({lst(h)} ++ [d]) {t0}) = true :=
  {proof}

end Snake9.WindowAutomaton
'''
        imports = '\n'.join(f'import WindowAutomaton7{T}Shard{i}_{t0}' for i in range(132) for t0 in range(1, 7))
        shape_lemmas = '\n\n'.join(f'''theorem shape7{T}_{i} : ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    allBelow (rgsBound {lst(h)} 0 + 1) (fun d => check7At tables7{T} ({lst(h)} ++ [d]) t0) = true := by
  intro t0 h1 h6
  rw [show rgsBound {lst(h)} 0 = {rgs_bound(h)} from rfl]
  have : t0 = 1 ∨ t0 = 2 ∨ t0 = 3 ∨ t0 = 4 ∨ t0 = 5 ∨ t0 = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
{chr(10).join(f'  · exact shard7{T}_{i}_{t0}' for t0 in range(1, 7))}''' for i, h in enumerate(shp))
        pres = rgs(6)
        # One kernel check per prefix of length 7 (at most 8 * 9 continuations): a whole prefix of
        # length 6 (up to 7 * 8 * 9 = 504 continuations) took 3.55 GB in one declaration on L417d.
        def pre_lemma(j, q):
            m = rgs_bound(q)
            parts = [f'''set_option maxRecDepth 100000 in
theorem shapesPre7{T}_{j}_{a} :
    allRGS 2 {max(m, a + 1)} (fun l => shapeTest7 shapes8_7{T} ({lst(q)} ++ {a} :: l)) = true := by
  decide +kernel''' for a in range(m + 1)]
            chain = 'rfl'
            for a in range(m + 1):
                chain = f'(allBelow_succ_of {a} _ {chain} shapesPre7{T}_{j}_{a})'
            parts.append(f'''theorem shapesPre7{T}_{j} :
    allRGS 3 (rgsBound {lst(q)} 0) (fun l => shapeTest7 shapes8_7{T} ({lst(q)} ++ l)) = true := by
  rw [show rgsBound {lst(q)} 0 = {m} from rfl]
  exact {chain}''')
            return '\n\n'.join(parts)
        pre_lemmas = '\n\n'.join(pre_lemma(j, q) for j, q in enumerate(pres))
        seq = f'''/-
Generated by {ME}.
Combines the {6 * len(shp)} shards of `tables7{T}` into `StepOK7 tables7{T}`.
-/
{imports}

set_option Elab.async false

namespace Snake9.WindowAutomaton

def shapePres7{T} : List (List Nat) := [{', '.join(lst(q) for q in pres)}]

{pre_lemmas}

set_option maxRecDepth 100000 in
/-- The 6-prefix checks, one `List.forall_mem_cons` step per prefix. -/
theorem shapesPres7{T} : ∀ pre ∈ shapePres7{T},
    allRGS 3 (rgsBound pre 0) (fun l => shapeTest7 shapes8_7{T} (pre ++ l)) = true := by
  unfold shapePres7{T}
{chr(10).join(f'  refine List.forall_mem_cons.2 ⟨shapesPre7{T}_{j}, ?_⟩' for j in range(len(pres)))}
  exact fun _ h => absurd h List.not_mem_nil

/-- Every induced restricted growth string of length 9 starts with a listed 8-shape (one
kernel check per prefix of length 7, combined per prefix of length 6). -/
theorem shapesCover7{T} : ShapesCover7 shapes8_7{T} = true :=
  allRGS_of_prefixes _ shapePres7{T} 6 3 9 rfl (by decide +kernel) shapesPres7{T}

{shape_lemmas}

-- One `List.forall_mem_cons` step per shape: `simp` on the membership disjunction of a
-- 203-element list hits the recursion limit (and passes 3.5 GB).
set_option maxRecDepth 100000 in
theorem shardsOK7{T} : ShardsOK7 tables7{T} shapes8_7{T} := by
  unfold ShardsOK7 shapes8_7{T}
{chr(10).join(f'  refine List.forall_mem_cons.2 ⟨shape7{T}_{i}, ?_⟩' for i in range(len(shp)))}
  exact fun _ h => absurd h List.not_mem_nil

theorem stepOK7{T} : StepOK7 tables7{T} := check7_of_shards _ _ shapesCover7{T} shardsOK7{T}

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.stepOK7{T}
'''
    out[os.path.join(a.out_stronger, f'WindowAutomaton7{T}Sequence.lean')] = seq
    if a.write == 'shards':
        out = {p: t for p, t in out.items() if os.path.basename(p).startswith(f'WindowAutomaton7{T}Shard')}
    for p, t in out.items():
        os.makedirs(os.path.dirname(p), exist_ok=True)
        if not (os.path.exists(p) and open(p).read() == t):
            open(p, 'w').write(t)
    sp = a.summary or os.path.join(DATA, f'auto7_{T}.json')
    os.makedirs(os.path.dirname(sp), exist_ok=True)
    json.dump(summary, open(sp, 'w'), indent=1)
    print(f'wrote {len(out)} modules; summary {sp}', flush=True)


if __name__ == '__main__':
    main()
