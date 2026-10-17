"""Generate the complete Lean chain for a direction-aware automaton (L, k, lambda = P/Q).

Emits, into work/spectral/stronger/ (suffix S = f'K{k}R{radius}'):
  WindowAutomaton{S}Data.lean      tables, check, shapes list
  WindowAutomaton{S}Shard{i}.lean  kernel check of the step table, one per canonical L-shape
  WindowAutomaton{S}Table.lean     membership lemma and check_of_rgs
  WindowAutomaton{S}Sequence.lean  transport, telescoping, total bound
  AggregateDirection{S}Conditional.lean   upper bound for Snake9.Snake

Also prints the module list for verify_strengthened.py.  Before writing it
re-implements the Lean check in Python on every shard transition.

  python gen_lean_automaton_k.py --index ../data/direction_certificates_k6.json --L 7 --k 6 --radius 3
"""
import argparse, itertools, json, os, sys
from fractions import Fraction as Fr
import numpy as np
sys.set_int_max_str_digits(0)
from refine import canon, induced
from refine_fast import FastAutomaton, prune, howard, bellman_ford, vertex_bound
from gen_lean_automaton import shape_code, sym_idx, rgs

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
STRONGER = os.path.join(ROOT, 'work', 'spectral', 'stronger')


class Listed:
    def __init__(self, keys):
        self.known = {k: 'UNSAT' for k in keys}

    def status(self, k):
        return self.known.get(k)


def cnt_idx(t):
    acc = 0
    for s in t:
        acc = acc * 6 + (s - 1)
    return acc


def ifchain(name, table, default):
    lines = [f'def {name} (c : Nat) : Nat :=']
    for code, i in sorted(table.items()):
        lines.append(f'  if c = {code} then {i} else')
    lines.append(f'  {default}')
    return '\n'.join(lines)


def lst(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index')
    ap.add_argument('--set', help='provisional: minimal-set JSON (solver answers, not certificates)')
    ap.add_argument('--L', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--radius', type=int, default=3)
    a = ap.parse_args()
    L, k = a.L, a.k
    S = f'K{k}R{a.radius}'
    if a.index:
        cases = [c for c in json.load(open(a.index))['cases'] if c['drat_trim_verified']]
        keys = [(tuple(c['dirs']), tuple(tuple(x) for x in c['alpha'])) for c in cases]
        source = os.path.basename(a.index)
    else:
        keys = [(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha'])) for e in json.load(open(a.set))['exclusions']]
        source = os.path.basename(a.set) + ' (PROVISIONAL: solver answers, not certificates)'
    A = FastAutomaton(L, k, 5)
    U, V, W, EXT = A.edges(Listed(keys))
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
    lam = Fr(int(W[cyc].sum()), len(cyc)); P, Q = lam.numerator, lam.denominator
    pi = bellman_ford(A.n, U, V, W, P, Q)
    assert pi is not None
    pi = pi - pi.min()
    assert pi.max() <= 15, pi.max()
    R = int(pi.max())
    vb = vertex_bound(A, U, V, W)
    C = P * L - Q * (L - 1) + R
    B = (9179 * Q + C - 8 * Q) // (P + 35 * Q)
    print(f'lambda {lam} range {R} dp-bound {vb-1} edges, potential-bound {B} edges', flush=True)

    shapes = A.shapes
    sidx = {shape_code(c): i for i, c in enumerate(shapes)}
    wshapes = sorted({kk[0] for kk in keys}, key=lambda c: (len(c), c))
    ws = {shape_code(c): i for i, c in enumerate(wshapes)}
    # Tables indexed by the base-6 code of the window symbols (digits sym-1, newest least
    # significant).  forwardT[(c, w)]: patterns of window shape w (c centres) in forward order;
    # reverseT[(c, w)]: the same patterns stored with symbols reversed, so that a window whose
    # *reversed* direction list has shape w is tested with its own (forward) symbol code.
    def code6(syms):
        acc = 0
        for t in syms:
            acc = acc * 6 + (t - 1)
        return acc
    forwardT, reverseT = {}, {}
    for dirs, alpha in keys:
        syms = [lo if lo == hi else 6 for lo, hi in alpha]
        cc = len(syms); w = ws[shape_code(dirs)]
        forwardT[(cc, w)] = forwardT.get((cc, w), 0) | (1 << code6(syms))
        reverseT[(cc, w)] = reverseT.get((cc, w), 0) | (1 << code6(syms[::-1]))
    M1 = 6 ** (k - 1)
    potX = {}
    for i, c in enumerate(shapes):
        acc = 0
        for t in range(M1):
            digs = [(t // 6 ** j) % 6 + 1 for j in range(k - 2, -1, -1)]
            acc |= min(R, int(pi[i * M1 + t])) << (4 * code6(digs))
        potX[i] = acc
    # ---- Vectorised Python mirror of the Lean step test --------------------
    ncodes = 6 ** k
    X = np.arange(ncodes)
    def tbl_bits(T, n):
        return np.array([(T >> j) & 1 for j in range(n)], bool) if T else np.zeros(n, bool)
    def pot_arr(i):
        return np.array([min(R, (potX[i] >> (4 * j)) & 15) for j in range(M1)])
    checked = 0
    for c0 in shapes:
        i0 = sidx[shape_code(c0)]
        for d in range(9):
            c = c0 + (d,)
            if not induced(c):
                continue
            blocked = np.zeros(ncodes, bool)
            for cc in range(2, k + 1):
                sub = c[L + 1 - (cc + 1):]
                F = ws.get(shape_code(tuple(canon(sub)))); V = ws.get(shape_code(tuple(canon(tuple(reversed(sub))))))
                code = X % (6 ** cc)
                if F is not None and (cc, F) in forwardT:
                    blocked |= tbl_bits(forwardT[(cc, F)], 6 ** cc)[code]
                if V is not None and (cc, V) in reverseT:
                    blocked |= tbl_bits(reverseT[(cc, V)], 6 ** cc)[code]
            i1 = sidx[shape_code(tuple(canon(c[1:])))]
            p0 = pot_arr(i0)[X // 6]; p1 = pot_arr(i1)[X % M1]; snew = X % 6 + 1
            ok = blocked | (Q * snew + p0 >= P + p1)
            assert ok.all(), (c,)
            checked += int((~blocked).sum())
    for c in rgs(L + 1):
        if induced(c):
            assert c[:L] in shapes and c[L] < 9
    print('python re-check passed on', checked, 'shard transitions', flush=True)

    # ---- Lean text helpers ---------------------------------------------------
    T = [f't{i}' for i in range(1, k)]                       # previous symbols
    allsym_open = ''.join(f'allSym (fun {v} => ' for v in T + ['s'])
    close = ')' * k
    win_terms = ' ||\n    '.join(
        f'wforb{S} (c.drop {L + 1 - (cc + 1)}) {lst(T[k - cc:] + ["s"])}' for cc in range(2, k + 1))
    ineq = (f'decide ({P} + pot{S} (c.drop 1) {lst(T[1:] + ["s"])} ≤ '
            f'{Q} * s + pot{S} (c.take {L}) {lst(T)})')
    def chain2(name, var1, var2, table):
        by_a = {}
        for (x, y), v in table.items():
            by_a.setdefault(x, {})[y] = v
        lines = [f'def {name} ({var1} {var2} : Nat) : Nat :=']
        for x in sorted(by_a):
            inner = ' else '.join(f'if {var2} = {y} then {v}' for y, v in sorted(by_a[x].items()))
            lines.append(f'  if {var1} = {x} then ({inner} else 0) else')
        lines.append('  0')
        return '\n'.join(lines)
    def chain1(name, var, table):
        lines = [f'def {name} ({var} : Nat) : Nat :=']
        for x, v in sorted(table.items()):
            lines.append(f'  if {var} = {x} then {v} else')
        lines.append('  0')
        return '\n'.join(lines)
    # window test arguments for stepN: for each c: F_c (forward shape idx), V_c (reversed shape idx)
    argnames = [f'{p}{cc}' for cc in range(2, k + 1) for p in ('F', 'V')] + ['i0', 'i1']
    wtests = ' ||\n    '.join(f'wtest{S} {cc} F{cc} V{cc} (x % {6 ** cc})' for cc in range(2, k + 1))
    data = f'''/-
Generated by milestones/10-window-aggregate/scripts/gen_lean_automaton_k.py.  Do not edit.
L = {L} directions of memory, k = {k} (windows of 2..{k} centres), radius {a.radius},
{len(keys)} exclusions (source: {source}), lambda = {P}/{Q}, potential range {R} on {A.n} states.

Tables are indexed by the base-6 code of the window symbols (digit = count-1, newest least
significant), so that inside the step loop every lookup is a truncation of the loop variable.
-/
import WindowAutomatonDefs

namespace Snake9.WindowAutomaton

{ifchain(f'shapeIdx{S}', sidx, len(shapes))}

{ifchain(f'wshapeIdx{S}', ws, len(wshapes))}

/-- Excluded patterns of window shape `w` with `c` centres, forward symbol order. -/
{chain2(f'forwardT{S}', 'c', 'w', forwardT)}

/-- Excluded patterns of window shape `w`, stored with the symbols reversed. -/
{chain2(f'reverseT{S}', 'c', 'w', reverseT)}

/-- Potential fields (4 bits) of shape `i`, indexed by the base-6 code of the {k - 1} counts. -/
{chain1(f'potX{S}', 'i', potX)}

/-- Base-6 code of a symbol list (digits sym-1, last symbol least significant). -/
def code6 : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => code6 l (acc * 6 + (s - 1))

def wtest{S} (c F V code : Nat) : Bool :=
  ((forwardT{S} c F >>> code) &&& 1 == 1) || ((reverseT{S} c V >>> code) &&& 1 == 1)

def ptest{S} (i code : Nat) : Nat := min {R} ((potX{S} i >>> (4 * code)) &&& 15)

def wsh{S} (ds : List Nat) : Nat := wshapeIdx{S} (shapeCode (canon ds))
def sh{S} (ds : List Nat) : Nat := shapeIdx{S} (shapeCode (canon ds))

/-- Is the window (directions `ds`, symbols `syms`) excluded, in either orientation? -/
def wforb{S} (ds syms : List Nat) : Bool := wtest{S} syms.length (wsh{S} ds) (wsh{S} ds.reverse) (code6 syms 0)

/-- Potential of a state. -/
def pot{S} (h t : List Nat) : Nat := ptest{S} (sh{S} h) (code6 t 0)

theorem pot{S}_le (h t : List Nat) : pot{S} h t ≤ {R} := Nat.min_le_left _ _

/-- Numeric step test: `x` encodes the {k - 1} previous symbols and the new one in base 6. -/
def stepN{S} ({' '.join(argnames)} x : Nat) : Bool :=
  {wtests} ||
  decide ({P} + ptest{S} i1 (x % {M1}) ≤ {Q} * (x % 6 + 1) + ptest{S} i0 (x / 6))

/-- Two-level enumeration of `[0, a*b)`: the kernel recursion depth stays at `a + b`. -/
def allBelow2 (a b : Nat) (p : Nat → Bool) : Bool :=
  allBelow a (fun i => allBelow b (fun j => p (i * b + j)))

theorem allBelow2_spec (a b : Nat) (p : Nat → Bool) (h : allBelow2 a b p = true) (x : Nat) (hx : x < a * b) :
    p x = true := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp at hx
    · exact hb
  have hi : x / b < a := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have h1 := allBelow_spec a _ h (x / b) hi
  have h2 := allBelow_spec b _ h1 (x % b) (Nat.mod_lt x hb)
  rwa [Nat.div_add_mod' x b] at h2

/-- Step test for one window of {L + 1} directions. -/
def check{S} (c : List Nat) : Bool :=
  !inducedPattern c ||
  allBelow2 {6 ** ((k + 1) // 2)} {6 ** (k // 2)} (stepN{S} {' '.join(f'(wsh{S} (c.drop {L + 1 - (cc + 1)})) (wsh{S} (c.drop {L + 1 - (cc + 1)}).reverse)' for cc in range(2, k + 1))}
    (sh{S} (c.take {L})) (sh{S} (c.drop 1)))

def shapes{S} : List (List Nat) := {lst(lst(c) for c in shapes)}

end Snake9.WindowAutomaton
'''
    open(os.path.join(STRONGER, f'WindowAutomaton{S}Data.lean'), 'w').write(data)
    for i, c in enumerate(shapes):
        open(os.path.join(STRONGER, f'WindowAutomaton{S}Shard{i}.lean'), 'w').write(f'''/-
Generated by gen_lean_automaton_k.py.  Shard {i}: shape {lst(c)} extended by every label below 9.
-/
import WindowAutomaton{S}Data

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000

{chr(10).join(f'theorem shard{S}_{i}_{d} : check{S} ({lst(c)} ++ [{d}]) = true := by decide +kernel' for d in range(9))}

/-- The nine labels combined; each piece is a separate kernel evaluation to bound memory. -/
theorem shard{S}_{i} : allBelow 9 (fun d => check{S} ({lst(c)} ++ [d])) = true := by
  simp only [allBelow, {', '.join(f'shard{S}_{i}_{d}' for d in range(9))}, Bool.and_self]

end Snake9.WindowAutomaton
''')
    rcases_pat = ' | '.join(['rfl'] * len(shapes))
    shard_apply = '\n'.join(f'    · exact allBelow_spec 9 _ shard{S}_{i} d hd' for i in range(len(shapes)))
    table = f'''/-
Generated by gen_lean_automaton_k.py.  Combines the {len(shapes)} shards.
-/
{chr(10).join(f'import WindowAutomaton{S}Shard{i}' for i in range(len(shapes)))}

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000

theorem rgs{S}_shape : allRGS {L + 1} 0 (fun c => !inducedPattern c ||
    (decide (c.take {L} ∈ shapes{S}) && (c.drop {L}).all (· < 9))) = true := by
  decide +kernel

theorem check{S}_of_rgs (c : List Nat) (hc : c.length = {L + 1}) (hr : isRGS c 0 = true) :
    check{S} c = true := by
  have hm := allRGS_spec {L + 1} 0 _ rgs{S}_shape c hc hr
  by_cases hind : inducedPattern c = true
  · rw [hind] at hm
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, decide_eq_true_eq] at hm
    obtain ⟨hmem, hlt⟩ := hm
    have hsplit : c = c.take {L} ++ c.drop {L} := (List.take_append_drop {L} c).symm
    have hlen : (c.drop {L}).length = 1 := by simp [hc]
    obtain ⟨d, hd7⟩ : ∃ d, c.drop {L} = [d] := by
      match h : c.drop {L}, hlen with
      | [d], _ => exact ⟨d, rfl⟩
    have hd : d < 9 := hlt d (by rw [hd7]; exact List.mem_singleton.mpr rfl)
    rw [hsplit, hd7]
    generalize hp : c.take {L} = pre at hmem ⊢
    simp only [shapes{S}, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    rcases hmem with {rcases_pat}
{shard_apply}
  · unfold check{S}
    simp [hind]

end Snake9.WindowAutomaton
'''
    open(os.path.join(STRONGER, f'WindowAutomaton{S}Table.lean'), 'w').write(table)

    # ---- Sequence module -----------------------------------------------------
    def dl(start, n):      # [d (i+start), ..., d (i+start+n-1)]
        return lst(f'd (i+{start + j})' if start + j else 'd i' for j in range(n))

    def al(start, n):      # [sym (a (i+start)), ...]
        return lst(f'sym (a (i+{start + j}))' for j in range(n))

    def dj(n):             # [d j, d (j+1), ...]
        return lst('d j' if j == 0 else f'd (j+{j})' for j in range(n))

    def aj(n):
        return lst(f'sym (a (j+{j + 1}))' for j in range(n))

    def dpj(n):
        return lst('pathDir p j' if j == 0 else f'pathDir p (j+{j})' for j in range(n))

    def apj(n):
        return lst(f'sym (countSeq p (j+{j + 1}))' for j in range(n))

    tvars = ' '.join(T)
    sym_t = [f'sym {v}' for v in T]
    hyps_raw = '\n'.join(
        f'    (hw{cc} : wforb{S} (x.drop {L + 1 - (cc + 1)}) {lst(sym_t[k - cc:] + ["sym s"])} = false)'
        for cc in range(2, k + 1))
    pos_raw = ' '.join(f'(h{i} : 1 ≤ {v})' for i, v in enumerate(T, 1)) + ' (hs : 1 ≤ s)'
    spec_chain = 'hc'
    for v, hv in list(zip(T, [f'h{i}' for i in range(1, k)])) + [('s', 'hs')]:
        spec_chain = f'allSym_spec _ ({spec_chain}) (sym {v}) (sym_ge_one _ {hv}) (sym_le_six _)'
    rw_list = ', '.join([f'wforb{S}_canon_drop'] * (k - 1) + [f'hw{cc}' for cc in range(2, k + 1)]
                        + [f'pot{S}_canon_drop', f'pot{S}_canon_take'])
    first = L - k + 1                                  # first previous-centre offset
    step_hyps = '\n'.join(
        f'    (hw{cc} : wforb{S} {dl(L - cc, cc + 1)} {al(L - cc + 1, cc)} = false)' for cc in range(2, k + 1))
    step_args_pos = ' '.join(f'(hpos (n+{first + j}) (by omega) (by omega))' for j in range(k))
    step_args_w = ' '.join(f'(hw{cc} (n+{L - cc}) (by omega))' for cc in range(2, k + 1))
    inv_hyps = '\n'.join(
        f'    (hw{cc} : ∀ j, j + {cc + 1} ≤ m → wforb{S} {dj(cc + 1)} {aj(cc)} = false)' for cc in range(2, k + 1))
    hw_names = ' '.join(f'hw{cc}' for cc in range(2, k + 1))
    pos_list = '\n'.join(f'    have := hpos {j} (by omega) (by omega)' for j in range(1, L))
    syms_all = sym_t + ['sym s']                           # oldest first
    # code = Σ (sym_j - 1) 6^(k-1-j)
    code_expr = ' + '.join(f'({v} - 1) * {6 ** (k - 1 - j)}' if j < k - 1 else f'({v} - 1)' for j, v in enumerate(syms_all))
    digit_binds = (f'have hs1 := sym_ge_one _ h1\n  ' if False else '') + \
        'have hsyms : ' + ' ∧ '.join(f'1 ≤ {v} ∧ {v} ≤ 6' for v in syms_all) + ' := ⟨' + \
        ', '.join(f'sym_ge_one _ {hv}, sym_le_six _' for hv in [f'h{i}' for i in range(1, k)] + ['hs']) + '⟩\n  ' + \
        f'let code := {code_expr}'
    # inside stepN: x % 6^c = code6 of the last c symbols; x / 6 = code6 of first k-1; x % M1 = code6 of last k-1; x % 6 + 1 = sym s
    code6_of = lambda syms: ' + '.join(f'({v} - 1) * {6 ** (len(syms) - 1 - j)}' if j < len(syms) - 1 else f'({v} - 1)' for j, v in enumerate(syms))
    eqs = []
    for cc in range(2, k + 1):
        eqs.append(f'have e{cc} : code % {6 ** cc} = {code6_of(syms_all[k - cc:])} := by omega')
    eqs.append(f'have e0 : code / 6 = {code6_of(syms_all[:k - 1])} := by omega')
    eqs.append(f'have e1 : code % {M1} = {code6_of(syms_all[1:])} := by omega')
    eqs.append(f'have es : code % 6 + 1 = sym s := by omega')
    digit_rewrites = '\n  '.join(eqs) + '\n  rw [' + ', '.join([f'e{cc}' for cc in range(2, k + 1)] + ['e0', 'e1', 'es']) + '] at h'
    # list codes: code6 [a, b, ...] 0 unfolds to the same polynomial
    code_rewrites = '\n  '.join(
        f'have c{cc} : code6 {lst(syms_all[k - cc:])} 0 = {code6_of(syms_all[k - cc:])} := by simp only [code6]; omega'
        for cc in range(2, k + 1)) + '\n  ' + \
        f'have c0 : code6 {lst(syms_all[:k - 1])} 0 = {code6_of(syms_all[:k - 1])} := by simp only [code6]; omega\n  ' + \
        f'have c1 : code6 {lst(syms_all[1:])} 0 = {code6_of(syms_all[1:])} := by simp only [code6]; omega\n  ' + \
        'rw [' + ', '.join([f'c{cc}' for cc in range(2, k + 1)] + ['c0', 'c1']) + '] at *'
    seq = f'''/-
Generated by gen_lean_automaton_k.py.  Sequence consequence for L = {L}, k = {k}, lambda = {P}/{Q}.
Core Lean only.
-/
import WindowAutomaton{S}Table
import WindowAutomatonSequence

namespace Snake9.WindowAutomaton

theorem wsh{S}_canon_drop (ds : List Nat) (n : Nat) : wsh{S} ((canon ds).drop n) = wsh{S} (ds.drop n) := by
  unfold wsh{S}; rw [canon_canon_drop]
theorem wsh{S}_canon_drop_rev (ds : List Nat) (n : Nat) :
    wsh{S} ((canon ds).drop n).reverse = wsh{S} (ds.drop n).reverse := by
  unfold wsh{S}; rw [canon_canon_drop_reverse]
theorem sh{S}_canon_drop (ds : List Nat) (n : Nat) : sh{S} ((canon ds).drop n) = sh{S} (ds.drop n) := by
  unfold sh{S}; rw [canon_canon_drop]
theorem sh{S}_canon_take (ds : List Nat) (n : Nat) : sh{S} ((canon ds).take n) = sh{S} (ds.take n) := by
  unfold sh{S}; rw [canon_canon_take]

theorem step{S}_raw (x : List Nat) (hx : x.length = {L + 1}) ({tvars} s : Nat)
    {pos_raw}
    (hind : inducedPattern x = true)
{hyps_raw} :
    {P} + pot{S} (x.drop 1) {lst(sym_t[1:] + ["sym s"])} ≤
      {Q} * sym s + pot{S} (x.take {L}) {lst(sym_t)} := by
  have hc := check{S}_of_rgs (canon x) (by rw [length_canon, hx]) (canon_isRGS x)
  unfold check{S} at hc
  rw [inducedPattern_canon, hind] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  rw [{', '.join([f'wsh{S}_canon_drop' , f'wsh{S}_canon_drop_rev'] * (k - 1) + [f'sh{S}_canon_take', f'sh{S}_canon_drop'])}] at hc
  {digit_binds}
  have hcode : code < {6 ** k} := by omega
  have h := allBelow2_spec {6 ** ((k + 1) // 2)} {6 ** (k // 2)} _ hc code (by omega)
  unfold stepN{S} at h
  {digit_rewrites}
  unfold pot{S} wforb{S} at *
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hw2 hw3 {' '.join(f'hw{cc}' for cc in range(4, k + 1))} ⊢
  {code_rewrites}
  rw [hw2, hw3, {', '.join(f'hw{cc}' for cc in range(4, k + 1))}] at h
  simpa using h

def win{S} (d : Nat → Nat) (i : Nat) : List Nat := {dl(0, L + 1)}
def hist{S} (d : Nat → Nat) (i : Nat) : List Nat := {dl(0, L)}
def syms{S} (a : Nat → Nat) (i : Nat) : List Nat := {al(first, k - 1)}

def Φ{S} (d a : Nat → Nat) (i : Nat) : Nat := pot{S} (hist{S} d i) (syms{S} a i)

theorem Φ{S}_le (d a : Nat → Nat) (i : Nat) : Φ{S} d a i ≤ {R} := pot{S}_le _ _

theorem step{S} (d a : Nat → Nat) (i : Nat)
    {' '.join(f'(h{j} : 1 ≤ a (i+{first + j}))' for j in range(k))}
    (hind : inducedPattern (win{S} d i) = true)
{step_hyps} :
    {P} + Φ{S} d a (i+1) ≤ {Q} * sym (a (i+{L})) + Φ{S} d a i := by
  have h := step{S}_raw (win{S} d i) rfl {' '.join(f'(a (i+{first + j}))' for j in range(k))}
    {' '.join(f'h{j}' for j in range(k))} hind {' '.join(f'hw{cc}' for cc in range(2, k + 1))}
  exact h

def S{S} (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => S{S} a n + sym (a (n+{L}))

theorem invariant{S} (d a : Nat → Nat) (m : Nat)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + {L + 1} ≤ m → inducedPattern (win{S} d i) = true)
{inv_hyps} :
    ∀ n, n + {L} ≤ m → {P} * n + Φ{S} d a n ≤ {Q} * S{S} a n + Φ{S} d a 0
  | 0, _ => by simp [S{S}]
  | n + 1, hn => by
    have ih := invariant{S} d a m hpos hind {hw_names} n (by omega)
    have hs := step{S} d a n {step_args_pos}
      (hind n (by omega)) {step_args_w}
    simp only [S{S}]
    omega

theorem sumA_ge{S} (a : Nat → Nat) (m : Nat) (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j) :
    ∀ n, n + {L} ≤ m → {L - 1} + S{S} a n ≤ sumA a (n + {L - 1})
  | 0, h => by
    simp only [S{S}, sumA, Nat.zero_add, Nat.reduceAdd]
{pos_list}
    omega
  | n + 1, h => by
    have ih := sumA_ge{S} a m hpos n (by omega)
    have := sym_le (a (n+{L}))
    show {L - 1} + (S{S} a n + sym (a (n+{L}))) ≤ sumA a (n+{L - 1}) + a (n+{L - 1}+1)
    have he2 : n + {L - 1} + 1 = n + {L} := by omega
    rw [he2]
    omega

theorem total_bound{S} (d a : Nat → Nat) (m : Nat) (hm : {L} ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + {L + 1} ≤ m → inducedPattern (win{S} d i) = true)
{inv_hyps} :
    {P} * m ≤ {Q} * sumA a (m - 1) + {C} := by
  have hinv := invariant{S} d a m hpos hind {hw_names} (m - {L}) (by omega)
  have hsum := sumA_ge{S} a m hpos (m - {L}) (by omega)
  have h0 := Φ{S}_le d a 0
  have he : m - {L} + {L - 1} = m - 1 := by omega
  rw [he] at hsum
  omega

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.total_bound{S}
'''
    open(os.path.join(STRONGER, f'WindowAutomaton{S}Sequence.lean'), 'w').write(seq)

    wr_hyps = '\n'.join(
        f'    (hw{cc} : ∀ j, j + {cc + 1} ≤ m → wforb{S} {dpj(cc + 1)}\n      {apj(cc)} = false)' for cc in range(2, k + 1))
    wrapper = f'''import WindowAutomaton{S}Sequence
import AggregateDirectionConditional

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

theorem win{S}_eq (p : Snake m) (i : Nat) : win{S} (pathDir p) i = blockList p i {L + 1} := rfl

/-- Conditional {B}-edge bound: no window of 2..{k} consecutive internal vertices has a
direction shape and lumped counts listed in `forbMask{S}` ({len(keys)} certified exclusions,
radius {a.radius}).  The premise is NOT proved in Lean; the unconditional bound remains 245. -/
theorem upper_{B}_of_direction_windows{S} {{m : Nat}} (p : Snake m)
{wr_hyps} : m ≤ {B} := by
  by_cases hm : m < {L}
  · omega
  obtain ⟨h0, h1, hpos, _, hid⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_bound{S} (pathDir p) (countSeq p) m (by omega) hpos'
    (fun i hi => by rw [win{S}_eq]; exact snake_inducedPattern_block p i {L + 1} hi) {hw_names}
  rw [sumA_eq_psum] at htot
  omega

#print axioms upper_{B}_of_direction_windows{S}
end
end Snake9
'''
    open(os.path.join(STRONGER, f'AggregateDirection{S}Conditional.lean'), 'w').write(wrapper)
    mods = [f'WindowAutomaton{S}Data'] + [f'WindowAutomaton{S}Shard{i}' for i in range(len(shapes))] + \
        [f'WindowAutomaton{S}Table', f'WindowAutomaton{S}Sequence', f'AggregateDirection{S}Conditional']
    json.dump({'suffix': S, 'L': L, 'k': k, 'radius': a.radius, 'lambda': str(lam), 'range': R,
               'bound_edges': B, 'dp_bound_edges': vb - 1, 'exclusions': len(keys), 'states': A.n,
               'shapes': len(shapes), 'modules': mods,
               'theorem': f'Snake9.upper_{B}_of_direction_windows{S}'},
              open(os.path.join(HERE, '..', 'data', f'lean_chain_{S}.json'), 'w'), indent=1)
    print('wrote', len(mods), 'modules; theorem', f'upper_{B}_of_direction_windows{S}')


if __name__ == '__main__':
    main()
