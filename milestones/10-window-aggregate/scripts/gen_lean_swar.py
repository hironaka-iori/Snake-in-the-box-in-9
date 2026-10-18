"""Lean chain for a direction-aware automaton with a word-parallel (SWAR) kernel check.

Same automaton and premises as gen_lean_automaton_k.py (L directions of memory, windows of
2..k centres, lump cap 5: symbols 1..6), but the kernel evaluates one field-wise comparison
of 216 packed 8-bit fields per outer step instead of a 36-iteration inner loop:

  * symbol codes x = Σ (sym-1) 6^j (newest symbol least significant); outer step h = x / 216
    (the k-3 oldest symbols); the three newest symbols (a, b, c) sit in field l = 36 c + 6 a + b;
  * window tables are stored "spread": bit 8 pos(z) + 7 for an excluded code z, with
    pos(z) = 216 (z / 216) + 36 (z % 6) + z / 6 % 36, so a window of 216 consecutive fields is a
    1728-bit slice of the table; two-centre tables carry the six copies the block needs;
  * potentials are 8-bit fields in natural order (potC) and, for the next state, transposed
    within 216-blocks (potT); the block of the previous state is replicated six times by one
    multiplication, the new symbol's weight is a constant pattern;
  * swarOK A B BL HI compares all 216 fields at once (WindowAutomatonSwar.lean).

Suffix: K{k}R{radius}W.

  python gen_lean_swar.py --index ../data/direction_certificates_k6.json --set ../data/minimal_L7_k6_K5_r3_fix.json --L 7 --k 6 --radius 3
"""
import argparse, itertools, json, os, sys
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
import numpy as np
from refine import canon, induced
from refine_fast import FastAutomaton, prune, howard, bellman_ford, vertex_bound
from gen_lean_automaton import shape_code, rgs
from gen_lean_automaton_k import Listed, ifchain, lst
from minimize_fast import sym_codes

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
STRONGER = os.path.join(ROOT, 'work', 'spectral', 'stronger')
NS = 6


def pos(z):
    return 216 * (z // 216) + 36 * (z % 6) + (z // 6) % 36


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index')
    ap.add_argument('--set')
    ap.add_argument('--L', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--radius', type=int, default=3)
    a = ap.parse_args()
    L, k, K = a.L, a.k, 5
    assert k >= 4, 'the SWAR block holds three symbols; use k >= 4'
    S = f'K{k}R{a.radius}W'
    CODE = f'code{S}'
    if a.index:
        cases = [c for c in json.load(open(a.index))['cases'] if c['drat_trim_verified']]
        keys = [(tuple(c['dirs']), tuple(tuple(x) for x in c['alpha'])) for c in cases]
        source = os.path.basename(a.index)
        if a.set:
            wanted = {(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha'])) for e in json.load(open(a.set))['exclusions']}
            missing = wanted - set(keys)
            assert not missing, f'{len(missing)} windows of the set are not certified'
            keys = [kk for kk in keys if kk in wanted]
            source = f'{os.path.basename(a.set)}, every window certified in {source}'
    else:
        keys = [(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha'])) for e in json.load(open(a.set))['exclusions']]
        source = os.path.basename(a.set) + ' (PROVISIONAL: solver answers, not certificates)'
    keys = [kk for kk in keys if len(sym_codes(kk[1], NS, K)) > 0]
    A = FastAutomaton(L, k, K)
    U, V, W, EXT = A.edges(Listed(keys))
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
    lam = Fr(int(W[cyc].sum()), len(cyc)); P, Q = lam.numerator, lam.denominator
    pi = bellman_ford(A.n, U, V, W, P, Q)
    assert pi is not None
    pi = pi - pi.min()
    R = int(pi.max())
    assert R <= 15 and P + R <= 128 and 6 * Q + R < 128, (P, Q, R)
    vb = vertex_bound(A, U, V, W)
    C = P * L - Q * (L - 1) + R
    B = (9179 * Q + C - 8 * Q) // (P + 35 * Q)
    print(f'lambda {lam} range {R} dp-bound {vb-1} edges, potential-bound {B} edges', flush=True)

    shapes = A.shapes
    sidx = {shape_code(c): i for i, c in enumerate(shapes)}
    wshapes = sorted({kk[0] for kk in keys}, key=lambda c: (len(c), c))
    ws = {shape_code(c): i for i, c in enumerate(wshapes)}

    def code6(syms):
        acc = 0
        for t in syms:
            acc = acc * NS + (t - 1)
        return acc

    def digits(code, cc):
        return [(code // NS ** j) % NS + 1 for j in range(cc - 1, -1, -1)]

    # bit tables (natural code order), then spread/permuted tables
    forwardB, reverseB = {}, {}
    for dirs, alpha in keys:
        cc = len(alpha); w = ws[shape_code(dirs)]
        for code in sym_codes(alpha, NS, K):
            forwardB[(cc, w)] = forwardB.get((cc, w), 0) | (1 << int(code))
            reverseB[(cc, w)] = reverseB.get((cc, w), 0) | (1 << code6(digits(int(code), cc)[::-1]))

    def spread(Fbits, cc):
        s = 0
        for z in range(NS ** cc):
            if Fbits >> z & 1:
                if cc == 2:
                    for aa in range(6):
                        s |= 1 << (8 * (36 * (z % 6) + 6 * aa + z // 6) + 7)
                else:
                    s |= 1 << (8 * pos(z) + 7)
        return s
    sfwd = {key: spread(v, key[0]) for key, v in forwardB.items()}
    srev = {key: spread(v, key[0]) for key, v in reverseB.items()}
    M1 = NS ** (k - 1)
    potC, potT = {}, {}
    for i, c in enumerate(shapes):
        vals = [min(R, int(pi[i * M1 + code6(digits(t, k - 1))])) for t in range(M1)]
        # vals[y] = potential of the state whose k-1 counts have natural code y
        potC[i] = sum(v << (8 * y) for y, v in enumerate(vals))
        potT[i] = sum(v << (8 * pos(y)) for y, v in enumerate(vals))

    # ---- Python mirror of the transition inequality (natural codes) --------------
    ncodes = NS ** k; X = np.arange(ncodes)

    def tbl_bits(Fbits, n):
        return np.array([(Fbits >> j) & 1 for j in range(n)], bool) if Fbits else np.zeros(n, bool)

    def pot_arr(i):
        return np.array([(potC[i] >> (8 * y)) & 255 for y in range(M1)])
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
                F = ws.get(shape_code(tuple(canon(sub)))); Vv = ws.get(shape_code(tuple(canon(tuple(reversed(sub))))))
                code = X % (NS ** cc)
                if F is not None and (cc, F) in forwardB:
                    blocked |= tbl_bits(forwardB[(cc, F)], NS ** cc)[code]
                if Vv is not None and (cc, Vv) in reverseB:
                    blocked |= tbl_bits(reverseB[(cc, Vv)], NS ** cc)[code]
            i1 = sidx[shape_code(tuple(canon(c[1:])))]
            p0 = pot_arr(i0)[X // NS]; p1 = pot_arr(i1)[X % M1]; snew = X % NS + 1
            ok = blocked | (Q * snew + p0 >= P + p1)
            assert ok.all(), (c,)
            checked += int((~blocked).sum())
    for c in rgs(L + 1):
        if induced(c):
            assert c[:L] in shapes and c[L] < 9
    # mirror of the SWAR semantics: for each (shape,d,h) the packed comparison equals the per-field truth
    print('python re-check passed on', checked, 'shard transitions', flush=True)

    # ---- Lean text ------------------------------------------------------------
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

    ONES = sum(1 << (8 * l) for l in range(216)); HI = 128 * ONES
    WPAT = sum((l // 36 + 1) << (8 * l) for l in range(216)); REP = sum(1 << (288 * i) for i in range(6))
    argn = [f'{p}{cc}' for cc in range(2, k + 1) for p in ('T', 'R')] + ['PC0', 'PT1']
    outer_lets = '  letN (blk T2 R2 ||| blk T3 R3 + 1) fun BL3 =>\n' + ''.join(
        f'  letN (blk T{cc} R{cc} + 1) fun M{cc} =>\n' for cc in range(4, k + 1))
    inner_lets = ''.join(
        f'    letN (winT M{cc} (1728 * (h % {NS ** (cc - 3)})) 1728 + 1) fun W{cc} =>\n' for cc in range(4, k + 1))
    blmask = ' ||| '.join(['BL3'] + [f'W{cc}' for cc in range(4, k + 1)])
    hp1 = f'(h % {NS ** (k - 4)})'
    check_args = '\n    '.join(
        f'(sfwd{S} {cc} (wsh{S} (c.drop {L - cc}))) (srev{S} {cc} (wsh{S} (c.drop {L - cc}).reverse))' for cc in range(2, k + 1))
    w2 = sorted({w for (cc, w) in sfwd if cc == 2} | {w for (cc, w) in srev if cc == 2})
    # per-table replication theorems for the two-centre tables, and the universal statement
    rep_thms = []
    for name, tbl in (('sfwd', sfwd), ('srev', srev)):
        for w in w2:
            if (2, w) in tbl:
                rep_thms.append(f'''theorem {name}{S}_rep_{w} : allBelowR 216 (fun l => Nat.testBit ({name}{S} 2 {w}) (8 * l + 7) == Nat.testBit ({name}{S} 2 {w}) (8 * (36 * (l / 36) + l % 6) + 7)) = true := by
  decide +kernel''')
    def rep_universal(name, tbl):
        ws2 = [w for w in w2 if (2, w) in tbl]
        cases = ''.join(f'''  by_cases h{w} : w = {w}
  · subst h{w}; exact eq_of_beq (allBelowR_spec _ _ {name}{S}_rep_{w} l hl)
''' for w in ws2)
        hyps = ', '.join(f'h{w}' for w in ws2)
        return f'''theorem {name}{S}_rep (w : Nat) : ∀ l, l < 216 →
    Nat.testBit ({name}{S} 2 w) (8 * l + 7) = Nat.testBit ({name}{S} 2 w) (8 * (36 * (l / 36) + l % 6) + 7) := by
  intro l hl
{cases}  have h0 : {name}{S} 2 w = 0 := by
    unfold {name}{S}
    simp [{hyps}]
  rw [h0]; simp'''
    # potential theorems
    pot_thms = []
    for i in range(len(shapes)):
        pot_thms.append(f'theorem potC{S}_bnd_{i} : allBelowR {M1} (fun y => Nat.ble (digit (potC{S} {i}) y) {R}) = true := by decide +kernel')
        pot_thms.append(f'theorem potT{S}_bnd_{i} : allBelowR {M1} (fun y => Nat.ble (digit (potT{S} {i}) y) {R}) = true := by decide +kernel')
        pot_thms.append(f'theorem potT{S}_cons_{i} : allBelowR {M1} (fun y => Nat.beq (digit (potT{S} {i}) (pos{S} y)) (digit (potC{S} {i}) y)) = true := by decide +kernel')
    def by_shape(name, body_i, default):
        cases = ''.join(f'''  by_cases h{i} : i = {i}
  · subst h{i}; {body_i(i)}
''' for i in range(len(shapes)))
        hyps = ', '.join(f'h{i}' for i in range(len(shapes)))
        return cases + f'''  have h0 : {name} i = 0 := by
    unfold {name}
    simp [{hyps}]
  {default}'''
    potC_le = f'''theorem potC{S}_digit_le (i y : Nat) (hy : y < {M1}) : digit (potC{S} i) y ≤ {R} := by
{by_shape(f'potC{S}', lambda i: f'exact Nat.le_of_ble_eq_true (allBelowR_spec _ _ potC{S}_bnd_{i} y hy)', f'rw [h0]; simp [digit]')}'''
    potT_le = f'''theorem potT{S}_digit_le (i y : Nat) (hy : y < {M1}) : digit (potT{S} i) y ≤ {R} := by
{by_shape(f'potT{S}', lambda i: f'exact Nat.le_of_ble_eq_true (allBelowR_spec _ _ potT{S}_bnd_{i} y hy)', f'rw [h0]; simp [digit]')}'''
    potT_eq = f'''theorem potT{S}_digit (i y : Nat) (hy : y < {M1}) : digit (potT{S} i) (pos{S} y) = digit (potC{S} i) y := by
{by_shape(f'potT{S}', lambda i: f'exact Nat.eq_of_beq_eq_true (allBelowR_spec _ _ potT{S}_cons_{i} y hy)', f'''have h0c : potC{S} i = 0 := by
    unfold potC{S}
    simp [{', '.join(f'h{i}' for i in range(len(shapes)))}]
  rw [h0, h0c]''')}'''
    # ---- spec lemma text
    bits = [f'Nat.testBit (blk T2 R2) (8 * pos{S} (code % 36) + 7)'] + \
        [f'Nat.testBit (blk T{cc} R{cc}) (8 * pos{S} (code % {NS ** cc}) + 7)' for cc in range(3, k + 1)]
    bool_or = bits[0]
    for bb in bits[1:]:
        bool_or = f'({bool_or} || {bb})'
    conclusion = (f'{bool_or} = true ∨\n      {P} + digit PT1 (216 * (code / 216 % {NS ** (k - 4)}) + pos{S} (code % 216)) ≤ '
                  f'{Q} * (code % 6 + 1) + digit PC0 (code / 6)')
    n_outer = 1 + (k - 3)                                  # BL3 and M4..Mk
    spec = f'''/-- One transition of the loop, for abstract tables. -/
theorem checkT{S}_spec ({' '.join(argn)} : Nat) (hc : checkT{S} {' '.join(argn)} = true)
    (code : Nat) (hcode : code < {NS ** k})
    (hb0 : ∀ y, y < {M1} → digit PC0 y ≤ {R}) (hb1 : ∀ y, y < {M1} → digit PT1 y ≤ {R})
    (h2f : ∀ l, l < 216 → Nat.testBit T2 (8 * l + 7) = Nat.testBit T2 (8 * (36 * (l / 36) + l % 6) + 7))
    (h2r : ∀ l, l < 216 → Nat.testBit R2 (8 * l + 7) = Nat.testBit R2 (8 * (36 * (l / 36) + l % 6) + 7)) :
    {conclusion} := by
  unfold checkT{S} at hc
  rw [{', '.join(['letN_succ'] * n_outer)}] at hc
  have h1 := allBelowR_spec _ _ hc (code / 216) (by omega)
  simp only [letN_succ] at h1
  have hl : pos{S} (code % 216) < 216 := by unfold pos{S}; omega
  -- A and B as packs of their fields
  have hA : winT PT1 (1728 * (code / 216 % {NS ** (k - 4)})) 1728 + {P} * ones{S}
      = pack (tab (fun l => digit PT1 (216 * (code / 216 % {NS ** (k - 4)}) + l) + {P}) 216) := by
    unfold winT
    rw [show 1728 * (code / 216 % {NS ** (k - 4)}) = 8 * (216 * (code / 216 % {NS ** (k - 4)})) by omega,
      show (1728 : Nat) = 8 * 216 by rfl, winT_pack, ones{S}_eq, pack_tab_mul, pack_tab_add]
    apply congrArg; apply tab_congr; intro j _; omega
  have hB : {Q} * wpat{S} + winT PC0 (288 * (code / 216)) 288 * rep{S}
      = pack (tab (fun l => {Q} * (l / 36 + 1) + digit PC0 (36 * (code / 216) + l % 36)) 216) := by
    unfold winT
    rw [show 288 * (code / 216) = 8 * (36 * (code / 216)) by omega, show (288 : Nat) = 8 * 36 by rfl,
      winT_pack, rep{S}_eq, ← pack_tab_rep, wpat{S}_eq, pack_tab_mul, pack_tab_add]
  rw [hA, hB, hi{S}_eq] at h1
  have key := swarOK_spec 216 _ _ _ _ _ rfl rfl
    (fun l hl' => by have := hb1 (216 * (code / 216 % {NS ** (k - 4)}) + l) (by omega); omega)
    (fun l hl' => by have := hb0 (36 * (code / 216) + l % 36) (by omega); omega) h1 _ hl
  sorry
'''
    data = f'''/-
Generated by milestones/10-window-aggregate/scripts/gen_lean_swar.py.  Do not edit.
L = {L} directions of memory, k = {k} (windows of 2..{k} centres), radius {a.radius},
{len(keys)} exclusions (source: {source}), lambda = {P}/{Q}, potential range {R} on {A.n} states.
Word-parallel kernel check: see the header of gen_lean_swar.py and WindowAutomatonSwar.lean.
-/
import WindowAutomatonDefs
import WindowAutomatonLoop
import WindowAutomatonSwar

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000

{ifchain(f'shapeIdx{S}', sidx, len(shapes))}

{ifchain(f'wshapeIdx{S}', ws, len(wshapes))}

/-- Stored position of a symbol code: the three newest symbols (a, b, c) go to field 36 c + 6 a + b. -/
def pos{S} (z : Nat) : Nat := 216 * (z / 216) + 36 * (z % 6) + z / 6 % 36

/-- Excluded patterns of window shape `w` with `c` centres: bit `8 * pos z + 7` for code `z`
(two-centre tables carry the six copies of each entry that a 216-field block needs). -/
{chain2(f'sfwd{S}', 'c', 'w', sfwd)}

/-- The same for windows whose reversed direction list has shape `w` (symbols reversed). -/
{chain2(f'srev{S}', 'c', 'w', srev)}

/-- Potential of shape `i`: 8-bit field `y` for the natural code `y` of the {k - 1} counts. -/
{chain1(f'potC{S}', 'i', potC)}

/-- The same potentials stored at `pos y`. -/
{chain1(f'potT{S}', 'i', potT)}

def {CODE} : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => {CODE} l (acc * 6 + (s - 1))

def wsh{S} (ds : List Nat) : Nat := wshapeIdx{S} (shapeCode (canon ds))
def sh{S} (ds : List Nat) : Nat := shapeIdx{S} (shapeCode (canon ds))

/-- Is the window (directions `ds`, symbols `syms`) excluded, in either orientation? -/
def wforb{S} (ds syms : List Nat) : Bool :=
  Nat.testBit (blk (sfwd{S} syms.length (wsh{S} ds)) (srev{S} syms.length (wsh{S} ds.reverse))) (8 * pos{S} ({CODE} syms 0) + 7)

/-- Potential of a state. -/
def pot{S} (h t : List Nat) : Nat := clip {R} (digit (potC{S} (sh{S} h)) ({CODE} t 0))

theorem pot{S}_le (h t : List Nat) : pot{S} h t ≤ {R} := clip_le _ _

def ones{S} : Nat := {ONES}
def hi{S} : Nat := {HI}
def wpat{S} : Nat := {WPAT}
def rep{S} : Nat := {REP}
theorem ones{S}_eq : ones{S} = pack (tab (fun _ => 1) 216) := by decide +kernel
theorem hi{S}_eq : hi{S} = pack (tab (fun _ => 128) 216) := by decide +kernel
theorem wpat{S}_eq : wpat{S} = pack (tab (fun l => l / 36 + 1) 216) := by decide +kernel
theorem rep{S}_eq : rep{S} = repK 36 6 := by decide +kernel

/-- All {NS ** k} symbol codes: outer loop over the {k - 3} oldest symbols, one packed
comparison of the 216 fields of the three newest per step. -/
def checkT{S} ({' '.join(argn)} : Nat) : Bool :=
{outer_lets}  allBelowR {NS ** (k - 3)} fun h =>
{inner_lets}    letN (winT PT1 (1728 * {hp1}) 1728 + {P} * ones{S} + 1) fun A =>
    letN ({Q} * wpat{S} + winT PC0 (288 * h) 288 * rep{S} + 1) fun B =>
    swarOK A B ({blmask}) hi{S}

{chr(10).join(rep_thms)}

{rep_universal('sfwd', sfwd)}

{rep_universal('srev', srev)}

{chr(10).join(pot_thms)}

{potC_le}

{potT_le}

{potT_eq}

/-- Step test for one window of {L + 1} directions. -/
def check{S} (c : List Nat) : Bool :=
  !inducedPattern c || checkT{S}
    {check_args}
    (potC{S} (sh{S} (c.take {L}))) (potT{S} (sh{S} (c.drop 1)))

def shapes{S} : List (List Nat) := {lst(lst(c) for c in shapes)}

end Snake9.WindowAutomaton
'''
    open(os.path.join(STRONGER, f'WindowAutomaton{S}Data.lean'), 'w').write(data)
    open(os.path.join(STRONGER, f'WindowAutomaton{S}Spec.lean'), 'w').write(f'''/-
Generated by gen_lean_swar.py: the extraction lemma for the packed check (abstract tables).
-/
import WindowAutomaton{S}Data

namespace Snake9.WindowAutomaton

{spec}
end Snake9.WindowAutomaton
''')
    print('wrote Data for', S, 'exclusions', len(keys), 'w2 shapes', w2)


if __name__ == '__main__':
    main()
