"""Generate the Lean data module for an (L=7, k=5, K=5) automaton (lambda = P/Q).

Same scheme as gen_lean_automaton.py, but the kernel check is sharded: one
theorem per canonical induced 7-direction shape (34 shards), each enumerating
the next label d < 9 and all 6^5 symbol combinations.  A kernel-checked
membership lemma shows that every induced restricted growth string of length 8
is one of those shapes followed by a label below 9, which combines the shards
into `check5_of_rgs`.

With `--tag T` every generated module and identifier carries the suffix `T`
(`WindowAutomaton5TData`, `check5T`, ...), so several certificate sets (the
radius-3 set of the bound 238, the radius-4 set of the bound 236) coexist; the
potential field is `--pot-bits` wide (4 for range 15, 6 for range 63), and the
lambda is taken from the minimum-mean cycle of the listed exclusions.

  python gen_lean_automaton5.py --index ../data/direction_certificates_k5.json
  python gen_lean_automaton5.py --index ../data/direction_certificates_r4.json --tag R4 --pot-bits 6
  python gen_lean_automaton5.py --set ../data/minimal_L7_k5_K5.json   # provisional, solver-only
"""
import argparse, itertools, json, os, sys
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
import numpy as np
from refine import Automaton, canon, prune, howard, exact_check, induced
from direction_bound import Listed
from gen_lean_automaton import shape_code, sym_idx, rgs

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
STRONGER = os.path.join(ROOT, 'work', 'spectral', 'stronger')
L, K_, KMAX = 7, 5, 5


def cnt_idx(t):
    acc = 0
    for s in t:
        acc = acc * 6 + (s - 1)
    return acc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index')
    ap.add_argument('--set')
    ap.add_argument('--tag', default='', help='suffix of the generated modules and identifiers')
    ap.add_argument('--pot-bits', type=int, default=4, help='width of the potential field (4 or 6)')
    a = ap.parse_args()
    T, BITS = a.tag, a.pot_bits
    MAXP = (1 << BITS) - 1
    OUT = os.path.join(STRONGER, f'WindowAutomaton5{T}Data.lean')
    if a.index:
        cases = [c for c in json.load(open(a.index))['cases'] if c['drat_trim_verified']]
        keys = [(tuple(c['dirs']), tuple(tuple(x) for x in c['alpha'])) for c in cases]
        source = os.path.basename(a.index)
    else:
        spec = json.load(open(a.set))
        keys = [(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha'])) for e in spec['exclusions']]
        source = os.path.basename(a.set) + ' (PROVISIONAL: solver answers, not certificates)'
    A = Automaton(L, K_, KMAX)
    print('states', A.n, flush=True)
    U, V, W, WIN = A.edges(Listed(keys))
    print('edges', len(U), flush=True)
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
    lam = Fr(int(W[cyc].sum()), len(cyc))
    P, Q = lam.numerator, lam.denominator
    print('lambda', lam, flush=True)
    pi = exact_check(A.n, U, V, W, P, Q)
    assert pi is not None
    pi = pi - pi.min()
    assert pi.max() <= MAXP, (pi.max(), MAXP)
    shapes7 = A.dstates
    s7 = {shape_code(c): i for i, c in enumerate(shapes7)}
    wshapes = sorted({k[0] for k in keys}, key=lambda c: (len(c), c))
    ws = {shape_code(c): i for i, c in enumerate(wshapes)}
    forb = 0
    for dirs, alpha in keys:
        syms = [lo if lo == hi else 6 for lo, hi in alpha]
        forb |= 1 << (ws[shape_code(dirs)] * 16807 + sym_idx(syms))
    pot = 0
    for (c, t), sid in A.sid.items():
        pot |= int(pi[sid]) << (BITS * (s7[shape_code(c)] * 1296 + cnt_idx(t)))

    def phi(h, t):
        code = shape_code(tuple(canon(h)))
        if code not in s7:
            return None
        return (pot >> (BITS * (s7[code] * 1296 + cnt_idx(t)))) & MAXP

    def wforb(ds, syms):
        def one(d, s):
            code = shape_code(tuple(canon(d)))
            return code in ws and (forb >> (ws[code] * 16807 + sym_idx(s))) & 1
        return one(ds, syms) or one(tuple(reversed(ds)), tuple(reversed(syms)))

    # Python mirror of check5 over shards (shape ++ [d], d < 9)
    checked = 0
    for c7 in shapes7:
        for d in range(9):
            c = c7 + (d,)
            if not induced(c):
                continue
            for t in itertools.product(range(1, 7), repeat=4):
                for s in range(1, 7):
                    al = t + (s,)
                    if any(wforb(c[8 - (k + 1):], al[4 - (k - 1):]) for k in (2, 3, 4, 5)):
                        continue
                    p0, p1 = phi(c[:7], t), phi(c[1:], al[1:])
                    assert p0 is not None and p1 is not None, (c, t, s)
                    assert Q * s + p0 >= P + p1, (c, t, s, p0, p1)
                    checked += 1
    # membership lemma mirror
    for c in rgs(8):
        if induced(c):
            assert c[:7] in shapes7 and c[7] < 9
    print('python re-check passed on', checked, 'shard transitions', flush=True)

    def ifchain(name, table, default):
        lines = [f'def {name} (c : Nat) : Nat :=']
        for code, i in sorted(table.items()):
            lines.append(f'  if c = {code} then {i} else')
        lines.append(f'  {default}')
        return '\n'.join(lines)

    stronger = STRONGER
    for i, c7 in enumerate(shapes7):
        lst = '[' + ', '.join(map(str, c7)) + ']'
        open(os.path.join(stronger, f'WindowAutomaton5{T}Shard{i}.lean'), 'w').write(f'''/-
Generated by milestones/10-window-aggregate/scripts/gen_lean_automaton5.py.  Shard {i} of the
step table: canonical 7-shape {lst} extended by every label below 9.
-/
import WindowAutomaton5{T}Data

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000 in
theorem shard{T}{i} : allBelow 9 (fun d => check5{T} ({lst} ++ [d])) = true := by
  decide +kernel

end Snake9.WindowAutomaton
''')
    shard_imports = '\n'.join(f'import WindowAutomaton5{T}Shard{i}' for i in range(len(shapes7)))
    shapes_list = '[' + ', '.join('[' + ', '.join(map(str, c)) + ']' for c in shapes7) + ']'
    rcases_pat = ' | '.join(['rfl'] * len(shapes7))
    shard_apply = '\n'.join(
        f'    · exact allBelow_spec 9 _ shard{T}{i} d hd' for i in range(len(shapes7)))

    src = f'''/-
Generated by milestones/10-window-aggregate/scripts/gen_lean_automaton5.py.
Do not edit by hand.  Tables: {len(keys)} window exclusions
(source: {source}), potential for lambda = {P}/{Q} on {A.n} states, range {int(pi.max())}.
-/
import WindowAutomatonDefs

namespace Snake9.WindowAutomaton

/-- Canonical induced 7-direction shapes. -/
{ifchain('shapeIdx7' + T, s7, len(shapes7))}

/-- Canonical window shapes (3 to 6 directions). -/
{ifchain('wshapeIdx5' + T, ws, len(wshapes))}

def forbMask5{T} : Nat := {forb}

def potMask5{T} : Nat := {pot}

def cntIdx5{T} : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => cntIdx5{T} l (acc * 6 + (s - 1))

def pot5{T} (h : List Nat) (t : List Nat) : Nat :=
  (potMask5{T} >>> ({BITS} * (shapeIdx7{T} (shapeCode (canon h)) * 1296 + cntIdx5{T} t 0))) &&& {MAXP}

def wforb5a{T} (ds : List Nat) (syms : List Nat) : Bool :=
  (forbMask5{T} >>> (wshapeIdx5{T} (shapeCode (canon ds)) * 16807 + symIdx syms 0)) &&& 1 == 1

def wforb5{T} (ds : List Nat) (syms : List Nat) : Bool :=
  wforb5a{T} ds syms || wforb5a{T} ds.reverse syms.reverse

/-- Step test for one eight-direction window `c`. -/
def check5{T} (c : List Nat) : Bool :=
  !inducedPattern c ||
  allSym (fun t1 => allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
    wforb5{T} (c.drop 5) [t4, s] || wforb5{T} (c.drop 4) [t3, t4, s] ||
    wforb5{T} (c.drop 3) [t2, t3, t4, s] || wforb5{T} (c.drop 2) [t1, t2, t3, t4, s] ||
    decide ({P} + pot5{T} (c.drop 1) [t2, t3, t4, s] ≤ {Q} * s + pot5{T} (c.take 7) [t1, t2, t3, t4]))))))

def shapes7{T} : List (List Nat) := {shapes_list}

theorem pot5{T}_le (h t : List Nat) : pot5{T} h t ≤ {MAXP} := by
  unfold pot5{T}
  exact Nat.le_of_lt_succ (Nat.and_lt_two_pow _ (by decide : {MAXP} < 2 ^ {BITS}))

end Snake9.WindowAutomaton
'''
    open(OUT, 'w').write(src)
    table = f'''/-
Generated by milestones/10-window-aggregate/scripts/gen_lean_automaton5.py.
Combines the {len(shapes7)} shards into the step test for every canonical window.
-/
{shard_imports}

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000

/-- Every induced restricted growth string of length 8 is a listed 7-shape followed by a label below 9. -/
theorem rgs8_shape{T} : allRGS 8 0 (fun c => !inducedPattern c ||
    (decide (c.take 7 ∈ shapes7{T}) && (c.drop 7).all (· < 9))) = true := by
  decide +kernel

theorem check5{T}_of_rgs (c : List Nat) (hc : c.length = 8) (hr : isRGS c 0 = true) : check5{T} c = true := by
  have hm := allRGS_spec 8 0 _ rgs8_shape{T} c hc hr
  by_cases hind : inducedPattern c = true
  · rw [hind] at hm
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, decide_eq_true_eq] at hm
    obtain ⟨hmem, hlt⟩ := hm
    have hsplit : c = c.take 7 ++ c.drop 7 := (List.take_append_drop 7 c).symm
    have hlen : (c.drop 7).length = 1 := by simp [hc]
    obtain ⟨d, hd7⟩ : ∃ d, c.drop 7 = [d] := by
      match h : c.drop 7, hlen with
      | [d], _ => exact ⟨d, rfl⟩
    have hd : d < 9 := hlt d (by rw [hd7]; exact List.mem_singleton.mpr rfl)
    rw [hsplit, hd7]
    generalize hp : c.take 7 = pre at hmem ⊢
    simp only [shapes7{T}, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    rcases hmem with {rcases_pat}
{shard_apply}
  · unfold check5{T}
    simp [hind]

end Snake9.WindowAutomaton
'''
    open(os.path.join(stronger, f'WindowAutomaton5{T}Table.lean'), 'w').write(table)
    print('wrote', OUT, 'exclusions', len(keys), 'shapes7', len(shapes7), 'wshapes', len(wshapes),
          'pot range', int(pi.max()))


if __name__ == '__main__':
    main()
