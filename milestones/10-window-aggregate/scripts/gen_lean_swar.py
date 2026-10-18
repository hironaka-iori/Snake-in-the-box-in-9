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

Suffix: K{k}R{radius}W (lump cap 5, six symbols); `--K 7` gives eight symbols, blocks of 512 fields and
suffix K{k}R{radius}C7W (the constants 6/36/216 above become NS/NS^2/NS^3).

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


def pos(z, NS):
    """Stored field of code `z`: the three newest base-NS digits (a, b, c) go to `N2 c + NS a + b`."""
    N2, N3 = NS * NS, NS ** 3
    return N3 * (z // N3) + N2 * (z % NS) + (z // NS) % N2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index')
    ap.add_argument('--set')
    ap.add_argument('--L', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--K', type=int, default=5, help='lump cap: symbols 1..K+1 (K+1 = count >= K+1)')
    a = ap.parse_args()
    L, k, K = a.L, a.k, a.K
    assert k >= 4, 'the SWAR block holds three symbols; use k >= 4'
    NS = K + 1; N2 = NS * NS; N3 = NS ** 3; B3 = 8 * N3; B2 = 8 * N2
    S = f'K{k}R{a.radius}W' if K == 5 else f'K{k}R{a.radius}C{K}W'
    CODE = f'code{S}'
    # names of the block-position lemmas and the symbol function (shared ones for NS = 6)
    POS = 'pos3' if NS == 6 else f'pos{S}'
    REPL = 'pack_tab_rep36' if NS == 6 else f'pack_tab_rep{S}'
    SYM = 'sym' if NS == 6 else f'symK {NS}'
    GE1 = (lambda h: f'sym_ge_one _ {h}') if NS == 6 else (lambda h: f'symK_ge_one {NS} _ (by decide) {h}')
    LEK = 'sym_le_six _' if NS == 6 else f'symK_le_K {NS} _'
    LE = 'sym_le' if NS == 6 else f'symK_le {NS}'
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
    assert R <= 15 and P + R <= 128 and NS * Q + R < 128, (P, Q, R)
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
                    for aa in range(NS):
                        s |= 1 << (8 * (N2 * (z % NS) + NS * aa + z // NS) + 7)
                else:
                    s |= 1 << (8 * pos(z, NS) + 7)
        return s
    sfwd = {key: spread(v, key[0]) for key, v in forwardB.items()}
    srev = {key: spread(v, key[0]) for key, v in reverseB.items()}
    M1 = NS ** (k - 1)
    potC, potT, potR = {}, {}, {}
    for i, c in enumerate(shapes):
        vals = [min(R, int(pi[i * M1 + code6(digits(t, k - 1))])) for t in range(M1)]
        # vals[y] = potential of the state whose k-1 counts have natural code y
        potC[i] = sum(v << (8 * y) for y, v in enumerate(vals))
        potT[i] = sum(v << (8 * pos(y, NS)) for y, v in enumerate(vals))
        # potR: every N2-field block of potC repeated NS times (field N3 h + l holds potC field N2 h + l % N2)
        potR[i] = sum(vals[N2 * (f // N3) + f % N2] << (8 * f) for f in range(NS ** k))

    # ---- Python mirror of the transition inequality (natural codes) --------------
    ncodes = NS ** k; X = np.arange(ncodes)

    def tbl_bits(Fbits, n):
        if not Fbits:
            return np.zeros(n, bool)
        raw = np.frombuffer(Fbits.to_bytes((n + 7) // 8, 'little'), dtype=np.uint8)
        return np.unpackbits(raw, bitorder='little')[:n].astype(bool)

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
    F = NS ** k                                            # fields of the full comparison
    ONES = sum(1 << (8 * l) for l in range(N3)); HI = 128 * ONES
    ONESP = sum(1 << (8 * l) for l in range(M1))
    WPAT = sum((l // N2 + 1) << (8 * l) for l in range(N3))
    def repk(n, m):
        return sum(1 << (8 * n * j) for j in range(m))
    ONESF, HIF = repk(N3, F // N3) * ONES, repk(N3, F // N3) * HI
    WPATF = repk(N3, F // N3) * WPAT
    REPB = repk(N2, NS)                                    # block replication inside consR
    REPA = repk(M1, NS)                                    # next-state table, repeated NS times
    REPC = {cc: repk(NS ** cc, NS ** (k - cc)) for cc in range(3, k)}   # window tables, c = 3..k-1
    print('python re-check passed on', checked, 'shard transitions', flush=True)
    # mirror of the packed check itself (big integers, exactly as `checkT` computes it)
    def swar_ok(A, Bv, BL, HIv):
        return ((((Bv + HIv) - A) & HIv) | BL) == HIv
    pairs = 0
    for c0 in shapes:
        i0 = sidx[shape_code(c0)]
        for d in range(9):
            c = c0 + (d,)
            if not induced(c):
                continue
            i1 = sidx[shape_code(tuple(canon(c[1:])))]
            tabs = {}
            for cc in range(2, k + 1):
                sub = c[L + 1 - (cc + 1):]
                Fw = ws.get(shape_code(tuple(canon(sub)))); Vw = ws.get(shape_code(tuple(canon(tuple(reversed(sub))))))
                tabs[cc] = sfwd.get((cc, Fw), 0) | srev.get((cc, Vw), 0)
            BL = (tabs[2] | tabs[3]) * REPC[3]
            for cc in range(4, k):
                BL |= tabs[cc] * REPC[cc]
            BL |= tabs[k]
            Av = potT[i1] * REPA + P * ONESF
            Bv = Q * WPATF + potR[i0]
            assert swar_ok(Av, Bv, BL, HIF), ('packed check fails', c)
            pairs += 1
    print('packed check mirrors', pairs, 'pairs', flush=True)

    # ---- Lean text ------------------------------------------------------------
    CHUNK = 8192

    def lit(v):
        """A numeral.  Lean parses a decimal literal digit by digit (quadratic in its length: a
        347,000-bit table costs four seconds), so large values are written as a list of 8192-bit
        chunks folded by `ofChunks`; the kernel rebuilds the numeral once per forced `letN`."""
        if v.bit_length() <= CHUNK:
            return str(v)
        chunks = []
        while v:
            chunks.append(v & ((1 << CHUNK) - 1))
            v >>= CHUNK
        return 'ofChunks [' + ', '.join(str(c) for c in chunks) + ']'

    def chain2(name, var1, var2, table):
        by_a = {}
        for (x, y), v in table.items():
            by_a.setdefault(x, {})[y] = v
        lines = [f'def {name} ({var1} {var2} : Nat) : Nat :=']
        for x in sorted(by_a):
            inner = ' else '.join(f'if {var2} = {y} then {lit(v)}' for y, v in sorted(by_a[x].items()))
            lines.append(f'  if {var1} = {x} then ({inner} else 0) else')
        lines.append('  0')
        return '\n'.join(lines)

    def chain1(name, var, table):
        lines = [f'def {name} ({var} : Nat) : Nat :=']
        for x, v in sorted(table.items()):
            lines.append(f'  if {var} = {x} then {lit(v)} else')
        lines.append('  0')
        return '\n'.join(lines)

    argn = [f'{p}{cc}' for cc in range(2, k + 1) for p in ('T', 'R')] + ['PR0', 'PT1']
    bl_terms = [f'(blk T2 R2 ||| blk T3 R3) * rep3{S}'] + \
        [f'blk T{cc} R{cc} * rep{cc}{S}' for cc in range(4, k)] + [f'blk T{k} R{k}']
    blmask = ' ||| '.join(bl_terms)
    check_args = '\n    '.join(
        f'(sfwd{S} {cc} (wsh{S} (c.drop {L - cc}))) (srev{S} {cc} (wsh{S} (c.drop {L - cc}).reverse))' for cc in range(2, k + 1))
    # size of the table of `cc` centres (two-centre tables carry copies up to N3 fields)
    def tsize(cc):
        return max(NS ** cc, N3)
    # per-table bounds and the universal statements (needed for the replication by multiplication)
    lt_thms = []
    def lt_universal(name, tbl, cc):
        ws_c = sorted(w for (c2, w) in tbl if c2 == cc)
        for w in ws_c:
            lt_thms.append(f'theorem {name}{S}_lt_{cc}_{w} : {name}{S} {cc} {w} < 2 ^ {8 * tsize(cc)} := by decide +kernel')
        cases = ''.join(f'''  by_cases hw{w} : w = {w}
  · subst hw{w}; exact {name}{S}_lt_{cc}_{w}
''' for w in ws_c)
        hyps = ', '.join(f'hw{w}' for w in ws_c)
        return f'''theorem {name}{S}_lt{cc} (w : Nat) : {name}{S} {cc} w < 2 ^ {8 * tsize(cc)} := by
{cases}  have h0 : {name}{S} {cc} w = 0 := by
    unfold {name}{S}
    simp [{hyps}]
  rw [h0]; exact Nat.two_pow_pos _'''
    lt_univ = [lt_universal(name, tbl, cc) for name, tbl in (('sfwd', sfwd), ('srev', srev)) for cc in range(2, k)]
    w2 = sorted({w for (cc, w) in sfwd if cc == 2} | {w for (cc, w) in srev if cc == 2})
    # per-table replication theorems for the two-centre tables, and the universal statement
    rep_thms = []
    for name, tbl in (('sfwd', sfwd), ('srev', srev)):
        for w in w2:
            if (2, w) in tbl:
                rep_thms.append(f'''theorem {name}{S}_rep_{w} : allBelowR {N3} (fun l => Nat.testBit ({name}{S} 2 {w}) (8 * l + 7) == Nat.testBit ({name}{S} 2 {w}) (8 * ({N2} * (l / {N2}) + l % {NS}) + 7)) = true := by
  decide +kernel''')
    def rep_universal(name, tbl):
        ws2 = [w for w in w2 if (2, w) in tbl]
        cases = ''.join(f'''  by_cases hw{w} : w = {w}
  · subst hw{w}; exact eq_of_beq (allBelowR_spec _ _ {name}{S}_rep_{w} l hl)
''' for w in ws2)
        hyps = ', '.join(f'hw{w}' for w in ws2)
        return f'''theorem {name}{S}_rep (w : Nat) : ∀ l, l < {N3} →
    Nat.testBit ({name}{S} 2 w) (8 * l + 7) = Nat.testBit ({name}{S} 2 w) (8 * ({N2} * (l / {N2}) + l % {NS}) + 7) := by
  intro l hl
{cases}  have h0 : {name}{S} 2 w = 0 := by
    unfold {name}{S}
    simp [{hyps}]
  rw [h0]; simp'''
    # potential theorems
    pot_thms = []
    for i in range(len(shapes)):
        for nm in ('potC', 'potT'):
            # Stated as the field bound itself: the mask test is kernel-evaluated against the
            # expected type (unifying a separately elaborated Bool statement overflows the stack).
            pot_thms.append(f'theorem {nm}{S}_bnd_{i} (y : Nat) (hy : y < {M1}) : digit ({nm}{S} {i}) y + {127 - R} < 128 :=\n'
                            f'  bytes_lt_of_masks _ _ _ _ _ hiP{S}_eq onesP{S}_eq (by decide) (by decide +kernel) y hy')
        # layout consistency, block by block: both {N3}-field windows are forced to numerals first,
        # so the inner loop divides small numbers only
        pot_thms.append(f'theorem potT{S}_cons_{i} : consT{S} (potT{S} {i}) (potC{S} {i}) = true := by decide +kernel')
        pot_thms.append(f'theorem potT{S}_lt_{i} : potT{S} {i} < 256 ^ {M1} := by decide +kernel')
        pot_thms.append(f'theorem potR{S}_lt_{i} : potR{S} {i} < 256 ^ {F} := by decide +kernel')
        pot_thms.append(f'theorem potR{S}_cons_{i} : consR{S} (potR{S} {i}) (potC{S} {i}) = true := by decide +kernel')
    def by_shape(name, body_i, default):
        cases = ''.join(f'''  by_cases hi{i} : i = {i}
  · subst hi{i}; {body_i(i)}
''' for i in range(len(shapes)))
        hyps = ', '.join(f'hi{i}' for i in range(len(shapes)))
        return cases + f'''  have h0 : {name} i = 0 := by
    unfold {name}
    simp [{hyps}]
  {default}'''
    potC_le = f'''theorem potC{S}_digit_le (i y : Nat) (hy : y < {M1}) : digit (potC{S} i) y ≤ {R} := by
{by_shape(f'potC{S}', lambda i: f'have h := potC{S}_bnd_{i} y hy; omega', f'rw [h0]; simp [digit]')}'''
    potT_le = f'''theorem potT{S}_digit_le (i y : Nat) (hy : y < {M1}) : digit (potT{S} i) y ≤ {R} := by
{by_shape(f'potT{S}', lambda i: f'have h := potT{S}_bnd_{i} y hy; omega', f'rw [h0]; simp [digit]')}'''
    potT_eq = f'''theorem potT{S}_digit (i y : Nat) (hy : y < {M1}) : digit (potT{S} i) ({POS} y) = digit (potC{S} i) y := by
{by_shape(f'potT{S}', lambda i: f'exact consT{S}_spec _ _ potT{S}_cons_{i} y hy', f'''have h0c : potC{S} i = 0 := by
    unfold potC{S}
    simp [{', '.join(f'hi{i}' for i in range(len(shapes)))}]
  rw [h0, h0c]; simp [digit]''')}'''
    potT_lt = f'''theorem potT{S}_lt (i : Nat) : potT{S} i < 256 ^ {M1} := by
{by_shape(f'potT{S}', lambda i: f'exact potT{S}_lt_{i}', f'rw [h0]; exact Nat.pow_pos (by decide)')}'''
    potR_lt = f'''theorem potR{S}_lt (i : Nat) : potR{S} i < 256 ^ {F} := by
{by_shape(f'potR{S}', lambda i: f'exact potR{S}_lt_{i}', f'rw [h0]; exact Nat.pow_pos (by decide)')}'''
    potR_eq = f'''theorem potR{S}_digit (i hb l : Nat) (hh : hb < {M1 // N2}) (hl : l < {N3}) :
    digit (potR{S} i) ({N3} * hb + l) = digit (potC{S} i) ({N2} * hb + l % {N2}) := by
{by_shape(f'potR{S}', lambda i: f'exact consR{S}_spec _ _ potR{S}_cons_{i} hb l hh hl', f'''have h0c : potC{S} i = 0 := by
    unfold potC{S}
    simp [{', '.join(f'hi{i}' for i in range(len(shapes)))}]
  rw [h0, h0c]; simp [digit]''')}'''
    # ---- spec lemma text
    bits = [f'Nat.testBit (blk T2 R2) (8 * {POS} (code % {N2}) + 7)'] + \
        [f'Nat.testBit (blk T{cc} R{cc}) (8 * {POS} (code % {NS ** cc}) + 7)' for cc in range(3, k + 1)]
    bool_or = bits[0]
    for bb in bits[1:]:
        bool_or = f'({bool_or} || {bb})'
    conclusion = (f'{bool_or} = true ∨\n      {P} + digit PT1 ({N3} * (code / {N3} % {NS ** (k - 4)}) + {POS} (code % {N3})) ≤ '
                  f'{Q} * (code % {NS} + 1) + digit PC0 (code / {NS})')
    # bits of the replicated window tables
    ew_haves = ''.join(f'''  have ew{cc} : Nat.testBit (blk T{cc} R{cc} * rep{cc}{S}) (8 * f + 7)
      = Nat.testBit (blk T{cc} R{cc}) (8 * {POS} (code % {NS ** cc}) + 7) := by
    rw [rep{cc}{S}_eq, testBit_mul_rep _ {NS ** cc} {NS ** (k - cc)} _ h{cc} (by omega)]
    have ps := {POS}_split code {NS ** (cc - 3)} (by decide)
    rw [show {N3} * {NS ** (cc - 3)} = {NS ** cc} by rfl] at ps
    have hidx : 8 * (f % {NS ** cc}) + 7 = 8 * {POS} (code % {NS ** cc}) + 7 := by rw [ps]; omega
    rw [hidx]
''' for cc in range(4, k))
    ew_names = ''.join(f', ew{cc}' for cc in range(4, k))
    ek = f'''  have ew{k} : Nat.testBit (blk T{k} R{k}) (8 * f + 7) = Nat.testBit (blk T{k} R{k}) (8 * {POS} (code % {NS ** k}) + 7) := by
    have ps := {POS}_split code {NS ** (k - 3)} (by decide)
    rw [show {N3} * {NS ** (k - 3)} = {NS ** k} by rfl] at ps
    have hidx : 8 * f + 7 = 8 * {POS} (code % {NS ** k}) + 7 := by rw [ps]; omega
    rw [hidx]
'''
    hlt_hyps = f'    (h3 : blk T2 R2 ||| blk T3 R3 < 2 ^ {8 * N3})' + ''.join(
        f' (h{cc} : blk T{cc} R{cc} < 2 ^ {8 * NS ** cc})' for cc in range(4, k))
    spec = f'''/-- The packed check implies the transition inequality for every code (abstract tables). -/
theorem checkT{S}_spec ({' '.join(argn)} PC0 : Nat) (hc : checkT{S} {' '.join(argn)} = true)
    (code : Nat) (hcode : code < {F})
    (hb0 : ∀ y, y < {M1} → digit PC0 y ≤ {R}) (hb1 : ∀ y, y < {M1} → digit PT1 y ≤ {R})
    (hT : PT1 < 256 ^ {M1}) (hRl : PR0 < 256 ^ {F})
    (hR : ∀ hb l, hb < {M1 // N2} → l < {N3} → digit PR0 ({N3} * hb + l) = digit PC0 ({N2} * hb + l % {N2}))
    (h2f : ∀ l, l < {N3} → Nat.testBit T2 (8 * l + 7) = Nat.testBit T2 (8 * ({N2} * (l / {N2}) + l % {NS}) + 7))
    (h2r : ∀ l, l < {N3} → Nat.testBit R2 (8 * l + 7) = Nat.testBit R2 (8 * ({N2} * (l / {N2}) + l % {NS}) + 7))
{hlt_hyps} :
    {conclusion} := by
  unfold checkT{S} at hc
  have hp : {POS} (code % {N3}) < {N3} := {POS}_lt code
  have hf : {N3} * (code / {N3}) + {POS} (code % {N3}) < {F} := by omega
  -- A and B as packs of their fields
  have hPT : PT1 * repK {M1} {NS} = pack (tab (fun l => digit PT1 (l % {M1})) {F}) := by
    have h := pack_tab_rep (digit PT1) {M1} {NS}
    rw [pack_tab_digit PT1 {M1} hT] at h
    exact h.symm
  have hA : PT1 * repA{S} + {P} * onesF{S} = pack (tab (fun l => {P} + digit PT1 (l % {M1})) {F}) := by
    rw [repA{S}_eq, hPT, onesF{S}_eq, pack_tab_mul, pack_tab_add]
    all_goals (apply congrArg; apply tab_congr; intro j _; first | rfl | omega)
  have hB : {Q} * wpatF{S} + PR0 = pack (tab (fun l => {Q} * (l % {N3} / {N2} + 1) + digit PR0 l) {F}) := by
    have hPR : PR0 = pack (tab (digit PR0) {F}) := (pack_tab_digit PR0 {F} hRl).symm
    conv => lhs; rw [hPR]
    rw [wpatF{S}_eq, pack_tab_mul, pack_tab_add]
    all_goals (apply congrArg; apply tab_congr; intro j _; first | rfl | omega)
  have key := swarOK_spec {F} (fun l => {P} + digit PT1 (l % {M1})) (fun l => {Q} * (l % {N3} / {N2} + 1) + digit PR0 l)
    _ _ _ _ hA hB hiF{S}_eq
    (fun l hl' => by dsimp only; have := hb1 (l % {M1}) (Nat.mod_lt _ (by decide)); omega)
    (fun l hl' => by
      dsimp only
      have e := hR (l / {N3}) (l % {N3}) (by omega) (Nat.mod_lt _ (by decide))
      rw [show {N3} * (l / {N3}) + l % {N3} = l by omega] at e
      rw [e]
      have := hb0 ({N2} * (l / {N3}) + l % {N3} % {N2}) (by omega)
      have : l % {N3} / {N2} < {NS} := by omega
      omega)
    hc _ hf
  simp only [Nat.testBit_or] at key
  generalize hfdef : {N3} * (code / {N3}) + {POS} (code % {N3}) = f at key hf
  have e23 : Nat.testBit ((blk T2 R2 ||| blk T3 R3) * rep3{S}) (8 * f + 7)
      = (Nat.testBit (blk T2 R2) (8 * {POS} (code % {N2}) + 7) || Nat.testBit (blk T3 R3) (8 * {POS} (code % {N3}) + 7)) := by
    rw [rep3{S}_eq, testBit_mul_rep _ {N3} {NS ** (k - 3)} _ h3 (by omega), show f % {N3} = {POS} (code % {N3}) by omega, Nat.testBit_or]
    have e2' : Nat.testBit (blk T2 R2) (8 * {POS} (code % {N3}) + 7) = Nat.testBit (blk T2 R2) (8 * {POS} (code % {N2}) + 7) := by
      rw [testBit_blk, testBit_blk, h2f _ hp, h2r _ hp, {POS}_div{N2}, {POS}_mod{NS}, {POS}_mod{N2}']
    rw [e2']
{ew_haves}{ek}  rw [e23{ew_names}, ew{k}] at key
  have e1 : f % {M1} = {N3} * (code / {N3} % {NS ** (k - 4)}) + {POS} (code % {N3}) := by omega
  have e2 : f % {N3} / {N2} + 1 = code % {NS} + 1 := by
    rw [show f % {N3} = {POS} (code % {N3}) by omega, {POS}_div{N2}]
  have e3 : digit PR0 f = digit PC0 (code / {NS}) := by
    have hR' := hR (code / {N3}) ({POS} (code % {N3})) (by omega) hp
    rw [hfdef, {POS}_mod{N2}] at hR'
    have hi : {N2} * (code / {N3}) + code / {NS} % {N2} = code / {NS} := by omega
    rw [hR', hi]
  rw [e1, e2, e3] at key
  exact key
'''
    pos_block = '' if NS == 6 else f'''
/-- Stored position of a symbol code: the three newest base-{NS} digits (a, b, c) of `z`
(c least significant) go to field `{N2} c + {NS} a + b` of their {N3}-block. -/
def {POS} (z : Nat) : Nat := {N3} * (z / {N3}) + {N2} * (z % {NS}) + z / {NS} % {N2}

theorem {POS}_mod{N3} (z : Nat) : {POS} (z % {N3}) = {N2} * (z % {NS}) + z / {NS} % {N2} := by
  unfold {POS}
  have h1 : z % {N3} / {N3} = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
  have h2 : z % {N3} % {NS} = z % {NS} := Nat.mod_mod_of_dvd z (by decide)
  have h3 : z % {N3} / {NS} % {N2} = z / {NS} % {N2} := by
    rw [show ({N3} : Nat) = {NS} * {N2} by rfl, Nat.mod_mul_right_div_self, Nat.mod_mod]
  rw [h1, h2, h3]
  omega

theorem {POS}_lt (z : Nat) : {POS} (z % {N3}) < {N3} := by rw [{POS}_mod{N3}]; omega

theorem {POS}_div{N2} (z : Nat) : {POS} (z % {N3}) / {N2} = z % {NS} := by rw [{POS}_mod{N3}]; omega

theorem {POS}_mod{N2} (z : Nat) : {POS} (z % {N3}) % {N2} = z / {NS} % {N2} := by rw [{POS}_mod{N3}]; omega

theorem {POS}_mod{NS} (z : Nat) : {POS} (z % {N3}) % {NS} = z / {NS} % {NS} := by rw [{POS}_mod{N3}]; omega

theorem {POS}_mod{N2}' (z : Nat) : {POS} (z % {N2}) = {N2} * (z % {NS}) + z / {NS} % {NS} := by
  unfold {POS}
  have h1 : z % {N2} / {N3} = 0 := Nat.div_eq_of_lt (by have := Nat.mod_lt z (by decide : 0 < {N2}); omega)
  have h2 : z % {N2} % {NS} = z % {NS} := Nat.mod_mod_of_dvd z (by decide)
  have h3 : z % {N2} / {NS} % {N2} = z / {NS} % {NS} := by
    rw [show ({N2} : Nat) = {NS} * {NS} by rfl, Nat.mod_mul_right_div_self]
    exact Nat.mod_eq_of_lt (by have := Nat.mod_lt (z / {NS}) (by decide : 0 < {NS}); omega)
  rw [h1, h2, h3]
  omega

theorem {POS}_split (z m : Nat) (hm : 0 < m) : {POS} (z % ({N3} * m)) = {N3} * (z / {N3} % m) + {POS} (z % {N3}) := by
  unfold {POS}
  have h1 : z % ({N3} * m) / {N3} = z / {N3} % m := Nat.mod_mul_right_div_self z {N3} m
  have h2 : z % ({N3} * m) % {NS} = z % {NS} := Nat.mod_mod_of_dvd z ⟨{N2} * m, by omega⟩
  have h3 : z % ({N3} * m) / {NS} % {N2} = z / {NS} % {N2} := by
    rw [show {N3} * m = {NS} * ({N2} * m) by omega, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
  have h4 : z % {N3} / {N3} = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
  have h5 : z % {N3} % {NS} = z % {NS} := Nat.mod_mod_of_dvd z (by decide)
  have h6 : z % {N3} / {NS} % {N2} = z / {NS} % {N2} := by
    rw [show ({N3} : Nat) = {NS} * {N2} by rfl, Nat.mod_mul_right_div_self, Nat.mod_mod]
  rw [h1, h2, h3, h4, h5, h6]
  omega

theorem {REPL} (f : Nat → Nat) : pack (tab (fun l => f (l % {N2})) {N3}) = pack (tab f {N2}) * repK {N2} {NS} :=
  pack_tab_rep f {N2} {NS}
'''
    data = f'''/-
Generated by milestones/10-window-aggregate/scripts/gen_lean_swar.py.  Do not edit.
L = {L} directions of memory, k = {k} (windows of 2..{k} centres), radius {a.radius},
{len(keys)} exclusions (source: {source}), lambda = {P}/{Q}, potential range {R} on {A.n} states.
Word-parallel kernel check: see the header of gen_lean_swar.py and WindowAutomatonSwar.lean.
-/
import WindowAutomatonDefs
import WindowAutomatonLoop
import WindowAutomatonSwar{chr(10) + 'import WindowAutomatonSym' if NS != 6 else ''}

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000
{pos_block}
{ifchain(f'shapeIdx{S}', sidx, len(shapes))}

{ifchain(f'wshapeIdx{S}', ws, len(wshapes))}

/-- Excluded patterns of window shape `w` with `c` centres: bit `8 * pos z + 7` for code `z`
(two-centre tables carry the {['', '', '', '', '', '', 'six', 'seven', 'eight', 'nine'][NS]} copies of each entry that a {N3}-field block needs). -/
{chain2(f'sfwd{S}', 'c', 'w', sfwd)}

/-- The same for windows whose reversed direction list has shape `w` (symbols reversed). -/
{chain2(f'srev{S}', 'c', 'w', srev)}

/-- Potential of shape `i`: 8-bit field `y` for the natural code `y` of the {k - 1} counts. -/
{chain1(f'potC{S}', 'i', potC)}

/-- The same potentials stored at `pos y`. -/
{chain1(f'potT{S}', 'i', potT)}

/-- The same potentials with every {N2}-field block repeated {NS} times (field `{N3} h + l` holds
field `{N2} h + l % {N2}` of `potC`). -/
{chain1(f'potR{S}', 'i', potR)}

def {CODE} : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => {CODE} l (acc * {NS} + (s - 1))

def wsh{S} (ds : List Nat) : Nat := wshapeIdx{S} (shapeCode (canon ds))
def sh{S} (ds : List Nat) : Nat := shapeIdx{S} (shapeCode (canon ds))

/-- Is the window (directions `ds`, symbols `syms`) excluded, in either orientation? -/
def wforb{S} (ds syms : List Nat) : Bool :=
  Nat.testBit (blk (sfwd{S} syms.length (wsh{S} ds)) (srev{S} syms.length (wsh{S} ds.reverse))) (8 * {POS} ({CODE} syms 0) + 7)

/-- Potential of a state. -/
def pot{S} (h t : List Nat) : Nat := clip {R} (digit (potC{S} (sh{S} h)) ({CODE} t 0))

theorem pot{S}_le (h t : List Nat) : pot{S} h t ≤ {R} := clip_le _ _

def ones{S} : Nat := {ONES}
def hi{S} : Nat := {HI}
def wpat{S} : Nat := {WPAT}
def onesP{S} : Nat := {lit(ONESP)}
def hiP{S} : Nat := {lit(128 * ONESP)}
def onesF{S} : Nat := {lit(ONESF)}
def hiF{S} : Nat := {lit(HIF)}
def wpatF{S} : Nat := {lit(WPATF)}
def repB{S} : Nat := {lit(REPB)}
def repA{S} : Nat := {lit(REPA)}
{chr(10).join(f'def rep{cc}{S} : Nat := {lit(REPC[cc])}' for cc in range(3, k))}
theorem ones{S}_eq : ones{S} = pack (tab (fun _ => 1) {N3}) := by decide +kernel
theorem hi{S}_eq : hi{S} = pack (tab (fun _ => 128) {N3}) := by decide +kernel
theorem wpat{S}_eq : wpat{S} = pack (tab (fun l => l / {N2} + 1) {N3}) := by decide +kernel
theorem onesF{S}_eq : onesF{S} = pack (tab (fun _ => 1) {F}) := by
  have h := pack_tab_rep (fun _ => 1) {N3} {F // N3}
  rw [← ones{S}_eq] at h
  have e : onesF{S} = ones{S} * repK {N3} {F // N3} := by decide +kernel
  rw [e]; exact h.symm
theorem hiF{S}_eq : hiF{S} = pack (tab (fun _ => 128) {F}) := by
  have h := pack_tab_rep (fun _ => 128) {N3} {F // N3}
  rw [← hi{S}_eq] at h
  have e : hiF{S} = hi{S} * repK {N3} {F // N3} := by decide +kernel
  rw [e]; exact h.symm
theorem wpatF{S}_eq : wpatF{S} = pack (tab (fun l => l % {N3} / {N2} + 1) {F}) := by
  have h := pack_tab_rep (fun l => l / {N2} + 1) {N3} {F // N3}
  rw [← wpat{S}_eq] at h
  have e : wpatF{S} = wpat{S} * repK {N3} {F // N3} := by decide +kernel
  rw [e]; exact h.symm
theorem repB{S}_eq : repB{S} = repK {N2} {NS} := by decide +kernel
theorem repA{S}_eq : repA{S} = repK {M1} {NS} := by decide +kernel
{chr(10).join(f'theorem rep{cc}{S}_eq : rep{cc}{S} = repK {NS ** cc} {NS ** (k - cc)} := by decide +kernel' for cc in range(3, k))}
theorem onesP{S}_eq : onesP{S} = pack (tab (fun _ => 1) {M1}) := by
  have h := pack_tab_rep (fun _ => 1) {N3} {M1 // N3}
  rw [← ones{S}_eq] at h
  have e : onesP{S} = ones{S} * repK {N3} {M1 // N3} := by decide +kernel
  rw [e]; exact h.symm
theorem hiP{S}_eq : hiP{S} = pack (tab (fun _ => 128) {M1}) := by
  have h := pack_tab_rep (fun _ => 128) {N3} {M1 // N3}
  rw [← hi{S}_eq] at h
  have e : hiP{S} = hi{S} * repK {N3} {M1 // N3} := by decide +kernel
  rw [e]; exact h.symm

/-- `T` holds the fields of `C` at the positions `{POS} y`, checked block by block on numerals. -/
def consT{S} (T C : Nat) : Bool :=
  allBelowR {M1 // N3} fun j =>
    letN (winT T ({B3} * j) {B3} + 1) fun WT =>
    letN (winT C ({B3} * j) {B3} + 1) fun WC =>
    allBelowR {N3} fun y => Nat.beq (digit WT ({N2} * (y % {NS}) + y / {NS})) (digit WC y)

theorem consT{S}_spec (T C : Nat) (h : consT{S} T C = true) (y : Nat) (hy : y < {M1}) :
    digit T ({POS} y) = digit C y := by
  unfold consT{S} at h
  have h1 := allBelowR_spec _ _ h (y / {N3}) (by omega)
  rw [letN_succ, letN_succ] at h1
  have h2 := Nat.eq_of_beq_eq_true (allBelowR_spec _ _ h1 (y % {N3}) (by omega))
  rw [show {B3} * (y / {N3}) = 8 * ({N3} * (y / {N3})) by omega, show ({B3} : Nat) = 8 * {N3} by rfl,
    digit_winT _ _ _ _ (by omega), digit_winT _ _ _ _ (by omega)] at h2
  rw [show {N3} * (y / {N3}) + y % {N3} = y by omega] at h2
  rw [← h2]
  congr 1
  unfold {POS}
  omega

/-- `Rt` holds every {N2}-field block of `C` {NS} times in a row (`potR` against `potC`). -/
def consR{S} (Rt C : Nat) : Bool :=
  allBelowR {M1 // N2} fun h => Nat.beq (winT Rt ({B3} * h) {B3}) (winT C ({B2} * h) {B2} * repB{S})

theorem consR{S}_spec (Rt C : Nat) (h : consR{S} Rt C = true) (hb l : Nat) (hh : hb < {M1 // N2}) (hl : l < {N3}) :
    digit Rt ({N3} * hb + l) = digit C ({N2} * hb + l % {N2}) := by
  unfold consR{S} at h
  have h1 := Nat.eq_of_beq_eq_true (allBelowR_spec _ _ h hb hh)
  have h2 := congrArg (fun X => digit X l) h1
  simp only at h2
  rw [show {B3} * hb = 8 * ({N3} * hb) by omega, show ({B3} : Nat) = 8 * {N3} by rfl, digit_winT _ _ _ _ hl] at h2
  rw [h2]
  unfold winT
  rw [show {B2} * hb = 8 * ({N2} * hb) by omega, show ({B2} : Nat) = 8 * {N2} by rfl, winT_pack, repB{S}_eq,
    ← pack_tab_rep, digit_pack _ (tab_bounded _ _ _ (fun _ _ => digit_lt _ _)) l, tab_getD _ _ l (by omega)]

/-- All {NS ** k} symbol codes at once: the next-state table repeated {NS} times, the
block-replicated current-state table, and the window tables replicated to {F} fields,
compared field-wise in one step. -/
def checkT{S} ({' '.join(argn)} : Nat) : Bool :=
  swarOK (PT1 * repA{S} + {P} * onesF{S}) ({Q} * wpatF{S} + PR0) ({blmask}) hiF{S}

{chr(10).join(rep_thms)}

{rep_universal('sfwd', sfwd)}

{rep_universal('srev', srev)}

{chr(10).join(lt_thms)}

{chr(10).join(lt_univ)}

{chr(10).join(pot_thms)}

{potC_le}

{potT_le}

{potT_eq}

{potT_lt}

{potR_lt}

{potR_eq}

/-- Step test for one window of {L + 1} directions. -/
def check{S} (c : List Nat) : Bool :=
  !inducedPattern c || checkT{S}
    {check_args}
    (potR{S} (sh{S} (c.take {L}))) (potT{S} (sh{S} (c.drop 1)))

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
    # ---- shards, table (same scheme as gen_lean_automaton_k.py) --------------
    for i, c in enumerate(shapes):
        open(os.path.join(STRONGER, f'WindowAutomaton{S}Shard{i}.lean'), 'w').write(f"""/-
Generated by gen_lean_swar.py.  Shard {i}: shape {lst(c)} extended by every label below 9.
-/
import WindowAutomaton{S}Data

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000

{chr(10).join(f'theorem shard{S}_{i}_{d} : check{S} ({lst(c)} ++ [{d}]) = true := by decide +kernel' for d in range(9))}

theorem shard{S}_{i} : allBelow 9 (fun d => check{S} ({lst(c)} ++ [d])) = true := by
  simp only [allBelow, {', '.join(f'shard{S}_{i}_{d}' for d in range(9))}, Bool.and_self]

end Snake9.WindowAutomaton
""")
    rcases_pat = ' | '.join(['rfl'] * len(shapes))
    shard_apply = '\n'.join(f'    · exact allBelow_spec 9 _ shard{S}_{i} d hd' for i in range(len(shapes)))
    open(os.path.join(STRONGER, f'WindowAutomaton{S}Table.lean'), 'w').write(f"""/-
Generated by gen_lean_swar.py.  Combines the {len(shapes)} shards.
-/
{chr(10).join(f'import WindowAutomaton{S}Shard{i}' for i in range(len(shapes)))}
import WindowAutomatonCode

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000

/-- Bitset of the shape codes: membership of a prefix is one bit test instead of a list search. -/
def shapeMask{S} : Nat := maskOf shapeCode shapes{S}

theorem shapes{S}_ok : shapes{S}.all (fun s => s.length == {L} && s.all (· < 8)) = true := by decide

/-- Every restricted growth string of length {L + 1} that passes the xor-mask induced test (a
consequence of `inducedPattern`, `inducedFast_of_inducedPattern`) is a listed shape followed by a
label below nine. -/
theorem rgs{S}_shape : letN (shapeMask{S} + 1) (fun M => allRGS {L + 1} 0 (fun c => !inducedFast c ||
    (Nat.testBit M (shapeCode (c.take {L})) && (c.drop {L}).all (· < 9)))) = true := by
  decide +kernel

theorem check{S}_of_rgs (c : List Nat) (hc : c.length = {L + 1}) (hr : isRGS c 0 = true) :
    check{S} c = true := by
  have hm := rgs{S}_shape
  rw [letN_succ] at hm
  have hm := allRGS_spec {L + 1} 0 _ hm c hc hr
  by_cases hind : inducedPattern c = true
  · have hfast := inducedFast_of_inducedPattern c
      (fun d hd => by have := isRGS_bound c 0 hr d hd; omega) hind
    rw [hfast] at hm
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, decide_eq_true_eq] at hm
    obtain ⟨hbit, hlt⟩ := hm
    obtain ⟨s, hs, hcode⟩ := testBit_maskOf _ _ _ hbit
    have hsh : s.length = {L} ∧ ∀ a, a ∈ s → a < 8 := by
      have hall := shapes{S}_ok
      simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
      exact hall s hs
    have hpre : (c.take {L}).length = {L} := by rw [List.length_take, hc]; decide
    have hr7 : isRGS (c.take {L}) 0 = true :=
      isRGS_append _ _ _ (by rw [List.take_append_drop]; exact hr)
    have hb7 : ∀ a, a ∈ c.take {L} → a < 8 := fun a ha => by
      have := isRGS_bound _ _ hr7 a ha; omega
    have hmem : c.take {L} ∈ shapes{S} := by
      unfold shapeCode at hcode
      rw [codeFrom_inj (c.take {L}) s 1 (by rw [hpre, hsh.1]) hb7 hsh.2 hcode.symm]; exact hs
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
""")

    # ---- Sequence module -----------------------------------------------------
    T = [f't{i}' for i in range(1, k)]
    def dl(start, n):
        return lst(f'd (i+{start + j})' if start + j else 'd i' for j in range(n))
    def al(start, n):
        return lst(f'{SYM} (a (i+{start + j}))' for j in range(n))
    def dj(n):
        return lst('d j' if j == 0 else f'd (j+{j})' for j in range(n))
    def aj(n):
        return lst(f'{SYM} (a (j+{j + 1}))' for j in range(n))
    def dpj(n):
        return lst('pathDir p j' if j == 0 else f'pathDir p (j+{j})' for j in range(n))
    def apj(n):
        return lst(f'{SYM} (countSeq p (j+{j + 1}))' for j in range(n))
    tvars = ' '.join(T)
    sym_t = [f'{SYM} {v}' for v in T]
    sym_s = f'{SYM} s'
    hyps_raw = '\n'.join(
        f'    (hw{cc} : wforb{S} (x.drop {L + 1 - (cc + 1)}) {lst(sym_t[k - cc:] + [sym_s])} = false)' for cc in range(2, k + 1))
    pos_raw = ' '.join(f'(h{i} : 1 ≤ {v})' for i, v in enumerate(T, 1)) + ' (hs : 1 ≤ s)'
    first = L - k + 1
    step_hyps = '\n'.join(
        f'    (hw{cc} : wforb{S} {dl(L - cc, cc + 1)} {al(L - cc + 1, cc)} = false)' for cc in range(2, k + 1))
    step_args_pos = ' '.join(f'(hpos (n+{first + j}) (by omega) (by omega))' for j in range(k))
    step_args_w = ' '.join(f'(hw{cc} (n+{L - cc}) (by omega))' for cc in range(2, k + 1))
    inv_hyps = '\n'.join(
        f'    (hw{cc} : ∀ j, j + {cc + 1} ≤ m → wforb{S} {dj(cc + 1)} {aj(cc)} = false)' for cc in range(2, k + 1))
    hw_names = ' '.join(f'hw{cc}' for cc in range(2, k + 1))
    pos_list = '\n'.join(f'    have := hpos {j} (by omega) (by omega)' for j in range(1, L))
    syms_all = sym_t + [sym_s]
    code_expr = ' + '.join(f'({v} - 1) * {NS ** (k - 1 - j)}' if j < k - 1 else f'({v} - 1)' for j, v in enumerate(syms_all))
    digit_binds = 'have hsyms : ' + ' ∧ '.join(f'1 ≤ {v} ∧ {v} ≤ {NS}' for v in syms_all) + ' := ⟨' + \
        ', '.join(f'{GE1(hv)}, {LEK}' for hv in [f'h{i}' for i in range(1, k)] + ['hs']) + '⟩\n  ' + \
        f'obtain ⟨code, hcd⟩ : ∃ code, code = {code_expr} := ⟨_, rfl⟩'
    code6_of = lambda syms: ' + '.join(f'({v} - 1) * {NS ** (len(syms) - 1 - j)}' if j < len(syms) - 1 else f'({v} - 1)' for j, v in enumerate(syms))
    eqs = [f'have e{cc} : code % {NS ** cc} = {code6_of(syms_all[k - cc:])} := by omega' for cc in range(k, 1, -1)]
    eqs.append(f'have e0 : code / {NS} = {code6_of(syms_all[:k - 1])} := by omega')
    eqs.append(f'have es : code % {NS} + 1 = {sym_s} := by omega')
    digit_rewrites = '\n  '.join(eqs) + '\n  rw [' + ', '.join([f'e{cc}' for cc in range(k, 1, -1)] + ['e0', 'es']) + '] at h'
    code_rewrites = '\n  '.join(
        f'have c{cc} : {CODE} {lst(syms_all[k - cc:])} 0 = {code6_of(syms_all[k - cc:])} := by simp only [{CODE}]; omega\n  rw [c{cc}] at hw{cc}'
        for cc in range(2, k + 1)) + '\n  ' + \
        f'have c0 : {CODE} {lst(syms_all[:k - 1])} 0 = {code6_of(syms_all[:k - 1])} := by simp only [{CODE}]; omega\n  ' + \
        f'have c1 : {CODE} {lst(syms_all[1:])} 0 = {code6_of(syms_all[1:])} := by simp only [{CODE}]; omega'
    seq = f"""/-
Generated by gen_lean_swar.py.  Sequence consequence for L = {L}, k = {k}, lambda = {P}/{Q}.
Core Lean only.
-/
import WindowAutomaton{S}Table
import WindowAutomaton{S}Spec
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
    {P} + pot{S} (x.drop 1) {lst(sym_t[1:] + [sym_s])} ≤
      {Q} * {sym_s} + pot{S} (x.take {L}) {lst(sym_t)} := by
  have hc := check{S}_of_rgs (canon x) (by rw [length_canon, hx]) (canon_isRGS x)
  unfold check{S} at hc
  rw [inducedPattern_canon, hind] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  rw [{', '.join([f'wsh{S}_canon_drop', f'wsh{S}_canon_drop_rev'] * (k - 1) + [f'sh{S}_canon_take', f'sh{S}_canon_drop'])}] at hc
  {digit_binds}
  have hcode : code < {NS ** k} := by omega
  have h := checkT{S}_spec {' '.join(['_'] * (2 * (k - 1) + 2))} (potC{S} (sh{S} (x.take {L}))) hc code hcode
    (fun y hy => potC{S}_digit_le _ y hy) (fun y hy => potT{S}_digit_le _ y hy) (potT{S}_lt _) (potR{S}_lt _)
    (fun hb l hh hl => potR{S}_digit _ hb l hh hl) (sfwd{S}_rep _) (srev{S}_rep _)
    (Nat.or_lt_two_pow (Nat.or_lt_two_pow (sfwd{S}_lt2 _) (srev{S}_lt2 _)) (Nat.or_lt_two_pow (sfwd{S}_lt3 _) (srev{S}_lt3 _)))
    {' '.join(f'(Nat.or_lt_two_pow (sfwd{S}_lt{cc} _) (srev{S}_lt{cc} _))' for cc in range(4, k))}
  have e1 : {N3} * (code / {N3} % {NS ** (k - 4)}) + {POS} (code % {N3}) = {POS} (code % {M1}) := by
    have ps := {POS}_split code {NS ** (k - 4)} (by decide)
    rw [show {N3} * {NS ** (k - 4)} = {M1} by rfl] at ps
    exact ps.symm
  rw [e1, potT{S}_digit _ _ (by omega)] at h
  unfold wforb{S} at {hw_names}
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at {hw_names}
  {code_rewrites}
  {digit_rewrites}
  rw [{', '.join(f'hw{cc}' for cc in range(2, k + 1))}] at h
  simp only [Bool.false_or, Bool.false_eq_true, false_or] at h
  unfold pot{S}
  rw [c0, c1]
  rw [clip_eq_of_le _ _ (potC{S}_digit_le _ _ (by omega)), clip_eq_of_le _ _ (potC{S}_digit_le _ _ (by omega))]
  exact h

def win{S} (d : Nat → Nat) (i : Nat) : List Nat := {dl(0, L + 1)}
def hist{S} (d : Nat → Nat) (i : Nat) : List Nat := {dl(0, L)}
def syms{S} (a : Nat → Nat) (i : Nat) : List Nat := {al(first, k - 1)}

def Φ{S} (d a : Nat → Nat) (i : Nat) : Nat := pot{S} (hist{S} d i) (syms{S} a i)

theorem Φ{S}_le (d a : Nat → Nat) (i : Nat) : Φ{S} d a i ≤ {R} := pot{S}_le _ _

theorem step{S} (d a : Nat → Nat) (i : Nat)
    {' '.join(f'(h{j} : 1 ≤ a (i+{first + j}))' for j in range(k))}
    (hind : inducedPattern (win{S} d i) = true)
{step_hyps} :
    {P} + Φ{S} d a (i+1) ≤ {Q} * {SYM} (a (i+{L})) + Φ{S} d a i := by
  have h := step{S}_raw (win{S} d i) rfl {' '.join(f'(a (i+{first + j}))' for j in range(k))}
    {' '.join(f'h{j}' for j in range(k))} hind {' '.join(f'hw{cc}' for cc in range(2, k + 1))}
  exact h

def S{S} (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => S{S} a n + {SYM} (a (n+{L}))

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
    have := {LE} (a (n+{L}))
    show {L - 1} + (S{S} a n + {SYM} (a (n+{L}))) ≤ sumA a (n+{L - 1}) + a (n+{L - 1}+1)
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
"""
    open(os.path.join(STRONGER, f'WindowAutomaton{S}Sequence.lean'), 'w').write(seq)
    wr_hyps = '\n'.join(
        f'    (hw{cc} : ∀ j, j + {cc + 1} ≤ m → wforb{S} {dpj(cc + 1)}\n      {apj(cc)} = false)' for cc in range(2, k + 1))
    wrapper = f"""import WindowAutomaton{S}Sequence
import AggregateDirectionConditional

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

theorem win{S}_eq (p : Snake m) (i : Nat) : win{S} (pathDir p) i = blockList p i {L + 1} := rfl

/-- Conditional {B}-edge bound: no window of 2..{k} consecutive internal vertices has a
direction shape and lumped counts listed in the tables of `WindowAutomaton{S}Data`
({len(keys)} certified exclusions, radius {a.radius}).  The premise is NOT proved in Lean; the
unconditional bound remains 245. -/
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
"""
    open(os.path.join(STRONGER, f'AggregateDirection{S}Conditional.lean'), 'w').write(wrapper)
    mods = ['WindowAutomatonLoop', 'WindowAutomatonSwar', 'WindowAutomatonCode'] + (['WindowAutomatonSym'] if NS != 6 else []) + \
        [f'WindowAutomaton{S}Data', f'WindowAutomaton{S}Spec'] + \
        [f'WindowAutomaton{S}Shard{i}' for i in range(len(shapes))] + \
        [f'WindowAutomaton{S}Table', f'WindowAutomaton{S}Sequence', f'AggregateDirection{S}Conditional']
    json.dump({'suffix': S, 'L': L, 'k': k, 'K': K, 'radius': a.radius, 'lambda': str(lam), 'range': R,
               'bound_edges': B, 'dp_bound_edges': vb - 1, 'exclusions': len(keys), 'states': A.n,
               'shapes': len(shapes), 'modules': mods, 'kernel_check': 'swar',
               'theorem': f'Snake9.upper_{B}_of_direction_windows{S}'},
              open(os.path.join(HERE, '..', 'data', f'lean_chain_{S}.json'), 'w'), indent=1)
    print('wrote', len(mods), 'modules; theorem', f'upper_{B}_of_direction_windows{S}', 'w2 shapes', w2)


if __name__ == '__main__':
    main()
