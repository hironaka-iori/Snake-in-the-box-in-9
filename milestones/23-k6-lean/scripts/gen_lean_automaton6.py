"""Generate the Lean data, shard and sequence modules of a six-centre (k = 6) automaton.

Six-centre version of `milestones/10-window-aggregate/scripts/gen_lean_automaton5.py`
for the generic Lean framework `work/spectral/stronger/WindowAutomaton6Defs.lean`:

  states    canonical induced 7-direction shape (34 of them) x 5 lumped counts (6^5),
            264,384 in all (the full product: no closed-set argument is needed in Lean);
  step      one more direction d < 9 and count s; the windows of 3..7 directions ending at
            the new vertex (2..6 counts) are tested against the exclusion table in both
            orientations; otherwise lambda + pot(next) <= s + pot(current) must hold.

Outputs (identifiers carry the tag T):

  work/final_lean/LocalWindowDirKeys6<T>.lean       `dirKeys6<T>`, `AllRefuted6<T>`
  work/spectral/stronger/WindowAutomaton6<T>Data.lean
        `tables6<T> : Tables6` (exclusion rows keyed by window shape and FIRST count,
        potential rows keyed by 7-shape and FIRST count) and `shapes7_6<T>`
  work/spectral/stronger/WindowAutomaton6<T>Shard<i>_<t0>.lean   (34 x 6 = 204 shards)
        `allBelow 9 (fun d => check6At tables6<T> (shape_i ++ [d]) t0) = true`
  work/spectral/stronger/WindowAutomaton6<T>Sequence.lean        `stepOK6<T> : StepOK tables6<T>`
  milestones/23-k6-lean/data/auto6_<T>.json                       summary for gen_lean_chain6.py

The potential is computed by integer Bellman-Ford on the full product for the given
lambda = P/Q (weights Q s - P); every table entry is decoded back and every transition is
re-checked in Python against the decoded tables before anything is written.  A shard
enumerates 9 x 6^5 = 69,984 transitions, as a five-centre shard does.

With --toy the potential is zero and lambda = 1 (every step test holds; the sequence
module uses `stepOK_of_trivial` and no shards are written): this exercises the data,
cover and chain modules on a small key set without any kernel enumeration of states.

  python gen_lean_automaton6.py --keys K.json [K2.json ...] --tag T --lam 4/1 [--provisional]
  python gen_lean_automaton6.py --keys toy_keys6.json --tag Toy --toy

Key files: {"keys": [[dirs, alpha], ...]} (k6_loop format), {"cases": [...]} (index
format, drat_trim_verified only) or {"exclusions": [{"dirs", "alpha"}]}.  An alpha entry
must be (s, s) with s <= 5 or (6, 21) (the lumped symbol 6 of `boundOf`); dirs must be a
restricted growth string of 3 to 7 directions.
"""
import argparse, itertools, json, os, sys, time
from fractions import Fraction as Fr
import numpy as np
sys.set_int_max_str_digits(0)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
STRONGER = os.path.join(ROOT, 'work', 'spectral', 'stronger')
CORE = os.path.join(ROOT, 'work', 'final_lean')
DATA = os.path.join(HERE, '..', 'data')
K5 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')
ME = 'milestones/23-k6-lean/scripts/gen_lean_automaton6.py'
NC = 6 ** 5          # count states per 7-shape
NT = 6 ** 6          # (state counts, new count)


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


def shape_code(l):
    acc = 1
    for a in l:
        acc = acc * 8 + a
    return acc


def sym_idx(syms):
    acc = 0
    for s in syms:
        acc = acc * 7 + s
    return acc


def cnt_idx(t):
    acc = 0
    for s in t:
        acc = acc * 6 + (s - 1)
    return acc


def rgs(n):
    out = []

    def go(m, l):
        if len(l) == n:
            out.append(tuple(l)); return
        for a in range(m + 1):
            go(max(m, a + 1), l + [a])
    go(0, [])
    return out


def sym_of(a):
    lo, hi = a
    if lo == hi and 1 <= lo <= 5:
        return lo
    if (lo, hi) == (6, 21):
        return 6
    raise SystemExit(f'count range {a} is not a lumped symbol (s,s) s<=5 or (6,21)')


def load_keys(paths):
    keys = set()
    for path in paths:
        d = json.load(open(path))
        if 'keys' in d:
            ents = [(e[0], e[1]) for e in d['keys']]
        elif 'cases' in d:
            ents = [(c['dirs'], c['alpha']) for c in d['cases'] if c['drat_trim_verified']]
        else:
            ents = [(e['dirs'], e['alpha']) for e in d['exclusions']]
        for dirs, alpha in ents:
            dirs = tuple(dirs)
            syms = tuple(sym_of(tuple(a)) for a in alpha)
            assert is_rgs(dirs) and 3 <= len(dirs) <= 7 and len(syms) + 1 == len(dirs), (dirs, syms)
            keys.add((dirs, syms))
    return sorted(keys, key=lambda k: (len(k[0]), k))


def build_tables(keys):
    wshapes = sorted({k[0] for k in keys}, key=lambda c: (len(c), c))
    widx = {shape_code(c): i for i, c in enumerate(wshapes)}
    forb = {}
    for dirs, syms in keys:
        r = widx[shape_code(dirs)]
        forb[(r, syms[0])] = forb.get((r, syms[0]), 0) | (1 << sym_idx(syms[1:]))
    return wshapes, widx, forb


def decode_rest(b, n):
    """Digits (base 7, n of them) of the bit index b."""
    out = []
    for _ in range(n):
        out.append(b % 7); b //= 7
    assert b == 0
    return tuple(reversed(out))


def forb_suffixes(widx, forb, nrows, dirs):
    """Lumped count tuples excluded on the window `dirs` by the emitted tables (forward
    lookup of `forbBit6`), decoded from the masks."""
    r = widx.get(shape_code(canon(dirs)), nrows)
    out = []
    for s0 in range(7):
        m = forb.get((r, s0), 0)
        while m:
            b = m.bit_length() - 1
            m ^= 1 << b
            out.append((s0,) + decode_rest(b, len(dirs) - 2))
    return out


def shapes7():
    return sorted({canon(ds) for ds in itertools.product(range(7), repeat=7) if induced(canon(ds))})


def transitions(shp, widx, forb, nrows):
    """For every 7-shape i and label d: (j, allowed) where j is the 7-shape of the target
    and allowed[x] for x = cnt_idx(t0..t4, s) says that no window of 3..7 directions
    ending at the new vertex is excluded (both orientations, as `wforb6`)."""
    s7 = {c: i for i, c in enumerate(shp)}
    out = []
    for i, c in enumerate(shp):
        for d in range(9):
            ds = c + (d,)
            if not induced(ds):
                continue
            j = s7[canon(ds[1:])]
            F = np.zeros((6,) * 6, bool)
            for w in range(2, 7):                    # w counts, w + 1 directions
                dirs = ds[-(w + 1):]
                cands = [t for t in forb_suffixes(widx, forb, nrows, dirs)]
                cands += [tuple(reversed(t)) for t in forb_suffixes(widx, forb, nrows, tuple(reversed(dirs)))]
                for t in cands:
                    if all(1 <= x <= 6 for x in t):
                        F[(slice(None),) * (6 - w) + tuple(x - 1 for x in t)] = True
            out.append((i, d, j, ~F.ravel()))
    return out


def bellman_ford(n, U, V, Wt, max_iter):
    order = np.argsort(V, kind='stable')
    Us, Vs, Ws = U[order], V[order], Wt[order]
    uv, starts = np.unique(Vs, return_index=True)
    pi = np.zeros(n, np.int64)
    for it in range(max_iter):
        cand = pi[Us] + Ws
        mins = np.minimum.reduceat(cand, starts)
        upd = mins < pi[uv]
        if not upd.any():
            return pi, it
        pi[uv[upd]] = mins[upd]
    return None, max_iter


def ifchain(name, table, default, arg='c'):
    lines = [f'def {name} ({arg} : Nat) : Nat :=']
    for code, i in sorted(table.items()):
        lines.append(f'  if {arg} = {code} then {i} else')
    lines.append(f'  {default}')
    return '\n'.join(lines)


def rowchain(name, rows, a='r', b='s'):
    """def name (r s : Nat) : Nat := if r = .. then (if s = .. then .. else ..) else .. 0"""
    by_r = {}
    for (r, s), m in sorted(rows.items()):
        if m:
            by_r.setdefault(r, []).append((s, m))
    lines = [f'def {name} ({a} {b} : Nat) : Nat :=']
    for r, ents in sorted(by_r.items()):
        inner = ' else '.join(f'if {b} = {s} then 0x{m:x}' for s, m in ents) + ' else 0'
        lines.append(f'  if {a} = {r} then ({inner}) else')
    lines.append('  0')
    return '\n'.join(lines)


def lst(c):
    return '[' + ', '.join(map(str, c)) + ']'


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--keys', nargs='+', required=True)
    ap.add_argument('--tag', required=True)
    ap.add_argument('--lam', help="lambda P/Q, or 'auto' for the minimum cycle mean (required unless --toy)")
    ap.add_argument('--toy', action='store_true')
    ap.add_argument('--provisional', action='store_true', help='keys are solver answers, not certificates')
    ap.add_argument('--max-iter', type=int, default=20000)
    ap.add_argument('--out-stronger', default=STRONGER)
    ap.add_argument('--out-core', default=CORE)
    ap.add_argument('--summary', default=None)
    ap.add_argument('--dry-run', action='store_true', help='compute and check, write nothing')
    a = ap.parse_args()
    T = a.tag
    t_start = time.time()
    keys = load_keys(a.keys)
    wshapes, widx, forb = build_tables(keys)
    nrows = len(wshapes)
    # decoding the masks gives back exactly the keys
    dec = set()
    for c in wshapes:
        for t in forb_suffixes(widx, forb, nrows, c):
            dec.add((c, t))
    assert dec == set(keys), 'mask decoding mismatch'
    shp = shapes7()
    assert len(shp) == 34
    for c in rgs(8):
        if induced(c):
            assert c[:7] in shp and c[7] < 9
    s7 = {shape_code(c): i for i, c in enumerate(shp)}
    print(f'{len(keys)} keys ({sum(len(k[1]) == 6 for k in keys)} six-centre), {nrows} window shapes, '
          f'{len(forb)} exclusion rows', flush=True)

    if a.toy:
        P, Q, B = 1, 1, 1
        pots = {}
        rng = 0
        iters = 0
    else:
        tr = transitions(shp, widx, forb, nrows)
        x = np.arange(NT)
        Us, Vs, Ss = [], [], []
        for i, d, j, ok in tr:
            xs = x[ok]
            Us.append(i * NC + xs // 6); Vs.append(j * NC + xs % NC); Ss.append(xs % 6 + 1)
        U = np.concatenate(Us).astype(np.int64); V = np.concatenate(Vs).astype(np.int64)
        S = np.concatenate(Ss).astype(np.int64)
        del Us, Vs, Ss
        n = len(shp) * NC
        if a.lam == 'auto':
            # minimum cycle mean of the full product (policy iteration of refine.py)
            sys.path.insert(0, K5)
            from refine import prune, howard
            keep = np.nonzero(prune(n, U, V))[0]
            mu, cyc = howard(n, U[keep], V[keep], S[keep])
            cyc = [keep[e] for e in cyc]
            lam = Fr(int(S[cyc].sum()), len(cyc))
            cnt = lambda x: [x // 6 ** k % 6 + 1 for k in range(4, -1, -1)]
            print(f'minimum cycle mean {lam} = {float(lam):.4f} on a {len(cyc)}-cycle; new counts '
                  f'{[int(S[e]) for e in cyc]}; states '
                  f'{[(lst(shp[U[e] // NC]), cnt(U[e] % NC)) for e in cyc]}', flush=True)
        else:
            lam = Fr(a.lam)
        P, Q = lam.numerator, lam.denominator
        print(f'{n} states, {len(U)} allowed transitions ({len(tr)} shape extensions); '
              f'Bellman-Ford for lambda = {P}/{Q}', flush=True)
        pi, iters = bellman_ford(n, U, V, Q * S - P, a.max_iter)
        if pi is None:
            raise SystemExit(f'no potential after {iters} rounds: lambda {P}/{Q} is above the '
                             f'minimum cycle mean of the full product (or raise --max-iter)')
        pi = pi - pi.min()
        rng = int(pi.max())
        B = max(1, rng.bit_length())
        assert (P + pi[V] <= Q * S + pi[U]).all()
        pots = {}
        for i in range(len(shp)):
            for t0 in range(1, 7):
                base = i * NC + (t0 - 1) * 6 ** 4
                row = 0
                for k in range(6 ** 4):          # k = cnt_idx(t1..t4)
                    row |= int(pi[base + k]) << (B * k)
                pots[(i, t0)] = row
        # mirror of `check6At`: decode the emitted potential rows and re-check every
        # transition (the exclusions were already decoded from the emitted masks)
        dec_pi = np.zeros(n, np.int64)
        for (i, t0), row in pots.items():
            base = i * NC + (t0 - 1) * 6 ** 4
            for k in range(6 ** 4):
                dec_pi[base + k] = (row >> (B * k)) & ((1 << B) - 1)
        assert (dec_pi == pi).all()
        assert (P + dec_pi[V] <= Q * S + dec_pi[U]).all()
        print(f'potential range {rng} ({B} bits), {iters} rounds; Python re-check passed on '
              f'{len(U)} transitions', flush=True)
        del U, V, S
    C = (2 ** B - 1) + 7 * P - 6 * Q
    N = (9171 * Q + C) // (P + 35 * Q)
    summary = dict(tag=T, keys=len(keys), six_centre=sum(len(k[1]) == 6 for k in keys), P=P, Q=Q,
                   bits=B, potential_range=rng, C=C, bound=N, toy=a.toy, provisional=a.provisional,
                   bf_rounds=iters, window_shapes=nrows, exclusion_rows=len(forb),
                   sources=[os.path.relpath(p, ROOT) for p in a.keys], seconds=round(time.time() - t_start),
                   rows=[[list(wshapes[r]), s0] for r, s0 in sorted(forb)])
    print(json.dumps({k: v for k, v in summary.items() if k != 'rows'}), flush=True)
    if a.dry_run:
        return
    src_note = ', '.join(summary['sources']) + (' (PROVISIONAL: solver answers, not certificates)'
                                                if a.provisional else '')

    CH = 400
    nch = max(1, (len(keys) + CH - 1) // CH)
    keys_mod = f'''import LocalWindowDirModel

/-!
# {len(keys)} window keys of the six-centre automaton `{T}`

Generated by `{ME}` from {src_note}.
Each key is a canonical direction list (restricted growth string, 3 to 7 directions) and
its lumped counts (`sym α = min α 6`); its certificate is `Refuted (winOf ds) (boundsOf syms)`.
-/

set_option maxHeartbeats 0

namespace Snake9.LocalWindow

''' + ''.join(f'''def dirKeys6{T}_{ci} : List (List Nat × List Nat) := [
''' + ',\n'.join(f'  ({lst(d)}, {lst(s)})' for d, s in keys[ci * CH:(ci + 1) * CH]) + ''']

''' for ci in range(nch)) + f'''/-- The keys, in chunks of {CH} (a single literal list of thousands of keys elaborates slowly). -/
def dirKeys6{T} : List (List Nat × List Nat) :=
  {' ++ '.join(f'dirKeys6{T}_{ci}' for ci in range(nch))}

/-- The {len(keys)} certificate statements of the six-centre automaton `{T}`. -/
def AllRefuted6{T} : Prop := AllRefutedList dirKeys6{T}

end Snake9.LocalWindow
'''
    potdef = (f'def potMask6{T} (r t0 : Nat) : Nat := 0' if a.toy else rowchain(f'potMask6{T}', pots, 'r', 't0'))
    data = f'''/-
Generated by {ME}.  Do not edit by hand.
Six-centre automaton `{T}`: {len(keys)} window exclusions ({src_note}),
lambda = {P}/{Q}, potential on {len(shp) * NC} states, range {rng} ({B}-bit fields).
-/
import WindowAutomaton6Defs

namespace Snake9.WindowAutomaton

/-- Canonical window shapes (3 to 7 directions) ↦ exclusion row. -/
{ifchain('wIdx6' + T, widx, nrows)}

/-- Exclusion rows: (window row, first count) ↦ mask over `symIdx` of the other counts. -/
{rowchain('forbMask6' + T, forb, 'r', 's')}

/-- Canonical induced 7-direction shapes ↦ potential row. -/
{ifchain('pIdx6' + T, s7, len(shp))}

/-- Potential rows: (7-shape, first count) ↦ {B}-bit fields at `cntIdx6` of the other four. -/
{potdef}

def tables6{T} : Tables6 where
  wIdx := wIdx6{T}
  forb := forbMask6{T}
  pIdx := pIdx6{T}
  pot := potMask6{T}
  bits := {B}
  num := {P}
  den := {Q}

def shapes7_6{T} : List (List Nat) := [{', '.join(lst(c) for c in shp)}]

/-- The nonzero exclusion rows (window shape, first count), for `cover6_rows`. -/
def rows6{T} : List (List Nat × Nat) := [{', '.join(f'({lst(wshapes[r])}, {s0})' for r, s0 in sorted(forb))}]

end Snake9.WindowAutomaton
'''
    out = {os.path.join(a.out_core, f'LocalWindowDirKeys6{T}.lean'): keys_mod,
           os.path.join(a.out_stronger, f'WindowAutomaton6{T}Data.lean'): data}
    if a.toy:
        seq = f'''/-
Generated by {ME} (--toy): the step test of `tables6{T}` holds trivially
(zero potential, lambda = 1), so no shards are needed.
-/
import WindowAutomaton6{T}Data

namespace Snake9.WindowAutomaton

theorem stepOK6{T} : StepOK tables6{T} := stepOK_of_trivial _ (fun _ _ => rfl) (by decide)

end Snake9.WindowAutomaton
'''
    else:
        for i, c in enumerate(shp):
            for t0 in range(1, 7):
                labels = []
                for d in range(9):
                    nm = f'shard6{T}_{i}_{t0}_{d}'
                    note = '' if induced(c + (d,)) else ' -- not induced: no transition'
                    labels.append(f'''set_option maxRecDepth 100000 in
theorem {nm} : check6At tables6{T} ({lst(c)} ++ [{d}]) {t0} = true := by
  decide +kernel{note}
''')
                out[os.path.join(a.out_stronger, f'WindowAutomaton6{T}Shard{i}_{t0}.lean')] = f'''/-
Generated by {ME}.  Shard ({i}, {t0}) of the step table of `tables6{T}`:
canonical 7-shape {lst(c)} extended by every label below 9, first count {t0}.
One kernel check per label (6^5 transitions each): the kernel caches live for one
declaration, so the peak memory is that of one label.
-/
import WindowAutomaton6{T}Data

set_option Elab.async false

namespace Snake9.WindowAutomaton

{chr(10).join(labels)}
theorem shard6{T}_{i}_{t0} : allBelow 9 (fun d => check6At tables6{T} ({lst(c)} ++ [d]) {t0}) = true :=
  allBelow9_of (fun d => check6At tables6{T} ({lst(c)} ++ [d]) {t0})
    {' '.join(f'shard6{T}_{i}_{t0}_{d}' for d in range(9))}

end Snake9.WindowAutomaton
'''
        imports = '\n'.join(f'import WindowAutomaton6{T}Shard{i}_{t0}' for i in range(len(shp)) for t0 in range(1, 7))
        shape_lemmas = '\n\n'.join(f'''theorem shape6{T}_{i} : ∀ t0, 1 ≤ t0 → t0 ≤ 6 →
    allBelow 9 (fun d => check6At tables6{T} ({lst(c)} ++ [d]) t0) = true := by
  intro t0 h1 h6
  have : t0 = 1 ∨ t0 = 2 ∨ t0 = 3 ∨ t0 = 4 ∨ t0 = 5 ∨ t0 = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
{chr(10).join(f'  · exact shard6{T}_{i}_{t0}' for t0 in range(1, 7))}''' for i, c in enumerate(shp))
        pres = rgs(5)
        pres_list = '[' + ', '.join(lst(q) for q in pres) + ']'
        pre_lemmas = '\n\n'.join(f'''set_option maxRecDepth 100000 in
theorem shapesPre6{T}_{j} :
    allRGS 3 (rgsBound {lst(q)} 0) (fun l => shapeTest6 shapes7_6{T} ({lst(q)} ++ l)) = true := by
  decide +kernel''' for j, q in enumerate(pres))
        seq = f'''/-
Generated by {ME}.
Combines the {6 * len(shp)} shards of `tables6{T}` into `StepOK tables6{T}`.
-/
{imports}

set_option Elab.async false

namespace Snake9.WindowAutomaton

{pre_lemmas}

/-- Every induced restricted growth string of length 8 is a listed 7-shape followed by a
label below 9 (one kernel check per prefix of length 5). -/
theorem shapesCover6{T} : ShapesCover shapes7_6{T} = true :=
  shapesCover_of _ {pres_list} 5 3 rfl (by decide +kernel) (by
    intro pre h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with {' | '.join(['rfl'] * len(pres))}
{chr(10).join(f'    · exact shapesPre6{T}_{j}' for j in range(len(pres)))})

{shape_lemmas}

theorem shardsOK6{T} : ShardsOK tables6{T} shapes7_6{T} := by
  intro h hh
  simp only [shapes7_6{T}, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with {' | '.join(['rfl'] * len(shp))}
{chr(10).join(f'  · exact shape6{T}_{i}' for i in range(len(shp)))}

theorem stepOK6{T} : StepOK tables6{T} := check6_of_shards _ _ shapesCover6{T} shardsOK6{T}

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.stepOK6{T}
'''
    out[os.path.join(a.out_stronger, f'WindowAutomaton6{T}Sequence.lean')] = seq
    for p, t in out.items():
        if not (os.path.exists(p) and open(p).read() == t):
            open(p, 'w').write(t)
    sp = a.summary or os.path.join(DATA, f'auto6_{T}.json')
    os.makedirs(os.path.dirname(sp), exist_ok=True)
    json.dump(summary, open(sp, 'w'), indent=1)
    print(f'wrote {len(out)} modules; summary {sp}', flush=True)


if __name__ == '__main__':
    main()
