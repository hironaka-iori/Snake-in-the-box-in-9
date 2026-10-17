"""Generate the Lean data module for the (L=7, k=5, K=5) automaton (lambda = 7/2).

Same scheme as gen_lean_automaton.py, but the kernel check is sharded: one
theorem per canonical induced 7-direction shape (34 shards), each enumerating
the next label d < 9 and all 6^5 symbol combinations.  A kernel-checked
membership lemma shows that every induced restricted growth string of length 8
is one of those shapes followed by a label below 9, which combines the shards
into `check5_of_rgs`.

  python gen_lean_automaton5.py --index ../data/direction_certificates_k5.json
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
OUT = os.path.join(ROOT, 'work', 'spectral', 'stronger', 'WindowAutomaton5Data.lean')
L, K_, KMAX = 7, 5, 5
P, Q = 7, 2


def cnt_idx(t):
    acc = 0
    for s in t:
        acc = acc * 6 + (s - 1)
    return acc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index')
    ap.add_argument('--set')
    a = ap.parse_args()
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
    assert lam == Fr(P, Q), lam
    pi = exact_check(A.n, U, V, W, P, Q)
    assert pi is not None
    pi = pi - pi.min()
    assert pi.max() <= 15, pi.max()
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
        pot |= int(pi[sid]) << (4 * (s7[shape_code(c)] * 1296 + cnt_idx(t)))

    def phi(h, t):
        code = shape_code(tuple(canon(h)))
        if code not in s7:
            return None
        return (pot >> (4 * (s7[code] * 1296 + cnt_idx(t)))) & 15

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

    shard_thms = []
    for i, c7 in enumerate(shapes7):
        lst = '[' + ', '.join(map(str, c7)) + ']'
        shard_thms.append(f'''theorem shard{i} : allBelow 9 (fun d => check5 ({lst} ++ [d])) = true := by
  decide +kernel''')
    shapes_list = '[' + ', '.join('[' + ', '.join(map(str, c)) + ']' for c in shapes7) + ']'
    rcases_pat = ' | '.join(['rfl'] * len(shapes7))
    shard_apply = '\n'.join(
        f'    · exact allBelow_spec 9 _ shard{i} d hd' for i in range(len(shapes7)))

    src = f'''/-
Generated by milestones/10-window-aggregate/scripts/gen_lean_automaton5.py.
Do not edit by hand.  Tables: {len(keys)} window exclusions
(source: {source}), potential for lambda = {P}/{Q} on {A.n} states, range {int(pi.max())}.
-/
import WindowAutomatonDefs

namespace Snake9.WindowAutomaton

/-- Canonical induced 7-direction shapes. -/
{ifchain('shapeIdx7', s7, len(shapes7))}

/-- Canonical window shapes (3 to 6 directions). -/
{ifchain('wshapeIdx5', ws, len(wshapes))}

def forbMask5 : Nat := {forb}

def potMask5 : Nat := {pot}

def cntIdx5 : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => cntIdx5 l (acc * 6 + (s - 1))

def pot5 (h : List Nat) (t : List Nat) : Nat :=
  (potMask5 >>> (4 * (shapeIdx7 (shapeCode (canon h)) * 1296 + cntIdx5 t 0))) &&& 15

def wforb5a (ds : List Nat) (syms : List Nat) : Bool :=
  (forbMask5 >>> (wshapeIdx5 (shapeCode (canon ds)) * 16807 + symIdx syms 0)) &&& 1 == 1

def wforb5 (ds : List Nat) (syms : List Nat) : Bool :=
  wforb5a ds syms || wforb5a ds.reverse syms.reverse

/-- Step test for one eight-direction window `c`. -/
def check5 (c : List Nat) : Bool :=
  !inducedPattern c ||
  allSym (fun t1 => allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
    wforb5 (c.drop 5) [t4, s] || wforb5 (c.drop 4) [t3, t4, s] ||
    wforb5 (c.drop 3) [t2, t3, t4, s] || wforb5 (c.drop 2) [t1, t2, t3, t4, s] ||
    decide ({P} + pot5 (c.drop 1) [t2, t3, t4, s] ≤ {Q} * s + pot5 (c.take 7) [t1, t2, t3, t4]))))))

def shapes7 : List (List Nat) := {shapes_list}

set_option maxRecDepth 100000

{chr(10).join(shard_thms)}

/-- Every induced restricted growth string of length 8 is a listed 7-shape followed by a label below 9. -/
theorem rgs8_shape : allRGS 8 0 (fun c => !inducedPattern c ||
    (decide (c.take 7 ∈ shapes7) && (c.drop 7).all (· < 9))) = true := by
  decide +kernel

theorem check5_of_rgs (c : List Nat) (hc : c.length = 8) (hr : isRGS c 0 = true) : check5 c = true := by
  have hm := allRGS_spec 8 0 _ rgs8_shape c hc hr
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
    simp only [shapes7, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    rcases hmem with {rcases_pat}
{shard_apply}
  · unfold check5
    simp [hind]

theorem pot5_le (h t : List Nat) : pot5 h t ≤ 15 := by
  unfold pot5
  exact Nat.le_of_lt_succ (Nat.and_lt_two_pow _ (by decide : 15 < 2 ^ 4))

end Snake9.WindowAutomaton
'''
    open(OUT, 'w').write(src)
    print('wrote', OUT, 'exclusions', len(keys), 'shapes7', len(shapes7), 'wshapes', len(wshapes),
          'pot range', int(pi.max()))


if __name__ == '__main__':
    main()
