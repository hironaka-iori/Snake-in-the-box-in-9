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

Large chains (L = 8, k = 7, K = 7: 132 shapes, 34.6M states):

  * automaton and potential on the memory-lean CSR graph (`--graph lean`, the default:
    lean_minimize.Graph / min_start_potential / bellman_ford, ~5 B per edge, 4.7 GB at L = 8);
    the Python mirrors work on numpy byte arrays (field by field, the stored layouts);
  * `--split` (auto above 2^22 states) writes Base / Pot<g> / Tab / Data instead of one Data
    module: numerals are elaboration-time literals (`nat_lit%`, WindowAutomatonLit: base-64 text
    for the potentials, sparse bit sets for the window tables, potT and potR computed while
    elaborating), the layout of potR is checked by the divide-and-conquer `consD`
    (WindowAutomatonConsD), the start table by blocks, the RGS enumeration of the Table module per
    prefix (WindowAutomatonRGS);
  * start table fields are min(127, D+ + Q * symbol sum) when the plain sum does not fit (always
    with --split), so any Q works; if the start-optimal potential does not fit the 8-bit transition
    fields (P + R <= 128, NS Q + R < 128), it is recomputed with its range capped;
  * k >= 7 Sequence modules do the digit arithmetic in small helper lemmas (omega in a clean
    context).

  python gen_lean_swar.py --set minimal_L8_k7_K7.json --L 8 --k 7 --K 7 --lam 9/2 --start --no-vb --outdir DIR --json-out DIR/chain.json

Field width (`--width auto`, the default): 8-bit fields when the potential fits them (P + R <= 128 and
NS Q + R < 128), otherwise 16-bit fields (P + R <= 32768, NS Q + R < 32768; split layout only).  The
16-bit chains use WindowAutomatonSwar16 / Transpose16 / ConsD16 / Lit16 (digit16, pack16, repK16,
swarOK16_spec, trans16, consD16, spreadBlocks16: the 8-bit statements with base 65536, field tops at
bit 16 l + 15, carry half 32768, start-table cap 32767), get the suffix ...W16, and put 4 shapes per
potential module by default (the numerals are twice as large).  The text is generated with the 8-bit
names and renamed on write (REN16), so the 8-bit output is unchanged.
"""
import argparse, itertools, json, os, sys, time
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
# the shared scripts (refine, minimize_fast, lean_automaton, ...); lean_minimize.py and enc.py may sit
# next to this file (a copy) or in the scripts directory
SCRIPTS = os.environ.get('WINDOW_SCRIPTS', HERE)
for _p in (SCRIPTS, HERE):
    if _p in sys.path:
        sys.path.remove(_p)
    sys.path.insert(0, _p)
from refine import canon, induced
from gen_lean_automaton import shape_code, rgs
from gen_lean_automaton_k import Listed, ifchain, lst
from minimize_fast import sym_codes

ROOT = os.path.abspath(os.path.join(SCRIPTS, '..', '..', '..'))
STRONGER = os.path.join(ROOT, 'work', 'spectral', 'stronger')
DATA_DIR = os.path.join(SCRIPTS, '..', 'data')


def pos(z, NS):
    """Stored field of code `z`: the three newest base-NS digits (a, b, c) go to `N2 c + NS a + b`."""
    N2, N3 = NS * NS, NS ** 3
    return N3 * (z // N3) + N2 * (z % NS) + (z // NS) % N2


# names of the width-dependent library lemmas: 8-bit (WindowAutomatonSwar, ...Transpose, ...ConsD,
# ...Lit) -> 16-bit (WindowAutomatonSwar16, ...Transpose16, ...ConsD16, ...Lit16)
REN16 = [(r'\bdigit_trans8\b', 'digit16_trans'), (r'\btrans8\b', 'trans16'), (r'\bswMask\b', 'swMask16'),
         (r'\bbytes_lt_of_masks\b', 'fields_lt_of_masks16'), (r'\bfield_le_of_swarOK\b', 'field_le_of_swarOK16'),
         (r'\bswarOK_spec\b', 'swarOK16_spec'), (r'\btestBit_mul_rep\b', 'testBit_mul_rep16'),
         (r'\bwinT_pack\b', 'winT_pack16'), (r'\bconsD_spec\b', 'consD16_spec'), (r'\bconsD\b', 'consD16'),
         (r'\bspreadBlocks\b', 'spreadBlocks16'), (r'\brepK_eq_div\b', 'repK16_eq_div'), (r'\brepK\b', 'repK16'),
         (r'\bpack\b', 'pack16'), (r'\bpack_', 'pack16_'), (r'\bdigit\b', 'digit16'), (r'\bdigit_', 'digit16_')]


class W16File:
    """A text file whose content gets the 16-bit library names on write."""
    def __init__(self, path):
        self.path = path

    def write(self, text):
        import re
        for pat, rep in REN16:
            text = re.sub(pat, rep, text)
        with open(self.path, 'w') as f:
            f.write(text)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index')
    ap.add_argument('--set')
    ap.add_argument('--L', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--K', type=int, default=5, help='lump cap: symbols 1..K+1 (K+1 = count >= K+1)')
    ap.add_argument('--transpose', choices=['swap', 'loop'], default='swap',
                    help='8-symbol chains: check the potT layout with six delta swaps (one big-number equality per '
                         'shape, WindowAutomatonTranspose) or field by field (the earlier loop, ~16 s per shape)')
    ap.add_argument('--potr', choices=['blocks', 'literal', 'computed'], default='blocks',
                    help='the block-replicated potentials: as the blocks of potC at the replicated stride times the '
                         'replicator (blocks; NS times less text than the full numeral), as full numerals, or computed '
                         'from potC by spreadR in the kernel (slower shards)')
    ap.add_argument('--start', action='store_true',
                    help='charge the start state its own symbols: potential chosen to minimise '
                         'D = max(pi - Q * symbol sum); constant L*P - Q*(L-k) + D instead of L*P - Q*(L-1) + R')
    ap.add_argument('--lam', help='prove the bound with this mean p/q (<= the minimum mean) instead of the minimum')
    ap.add_argument('--outdir', default=STRONGER, help='directory of the generated Lean modules')
    ap.add_argument('--json-out', help='chain description JSON (default ../data/lean_chain_<suffix>.json)')
    ap.add_argument('--graph', choices=['lean', 'fast'], default='lean',
                    help='automaton and potential: memory-lean CSR graph (lean_minimize.Graph, C Bellman-Ford, '
                         '~5 B/edge) or FastAutomaton (numpy, ~68 B/edge); both give the same potential')
    ap.add_argument('--no-vb', action='store_true', help='skip the walk bound (dp_bound_edges: null)')
    ap.add_argument('--split', choices=['auto', 'yes', 'no'], default='auto',
                    help='large chains (auto: more than 2^22 states): tables as elaboration-time numerals '
                         '(WindowAutomatonLit), potentials in per-group modules, divide-and-conquer layout checks')
    ap.add_argument('--group', type=int, help='--split: shapes per potential module (default 12 for 8-bit fields, '
                    '4 for 16-bit fields)')
    ap.add_argument('--width', choices=['auto', '8', '16'], default='auto',
                    help='bits per SWAR field: auto = 8 when the potential fits 8-bit fields (P + R <= 128, '
                         'NS Q + R < 128), else 16 (P + R <= 32768, NS Q + R < 32768; --split chains only); '
                         'a forced width caps the potential range when it does not fit')
    a = ap.parse_args()
    L, k, K = a.L, a.k, a.K
    assert k >= 4, 'the SWAR block holds three symbols; use k >= 4'
    NS = K + 1; N2 = NS * NS; N3 = NS ** 3; B3 = 8 * N3; B2 = 8 * N2
    # radius label: the radii of the balls that refute the listed windows (two-level oracle sets
    # name them per exclusion), e.g. R3 or R34
    radii = {a.radius}
    if a.set:
        radii |= {e.get('radius', a.radius) for e in json.load(open(a.set))['exclusions']}
    RL = ''.join(str(r) for r in sorted(radii))
    S = f'K{k}R{RL}W' if K == 5 else f'K{k}R{RL}C{K}W'
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
    OUT = a.outdir
    os.makedirs(OUT, exist_ok=True)
    T0 = time.time()

    def fits(w, R_):
        # w-bit fields: next-state field P + pot <= 2^(w-1), current-state field NS Q + pot < 2^(w-1)
        return P + R_ <= 1 << (w - 1) and NS * Q + R_ < 1 << (w - 1)

    def choose_width(R_):
        if a.width != 'auto':
            return int(a.width)
        return 8 if fits(8, R_) else 16
    if a.graph == 'fast':
        from refine_fast import FastAutomaton, prune, bellman_ford, vertex_bound
        A = FastAutomaton(L, k, K)
        U, V, W, EXT = A.edges(Listed(keys))
        m = prune(A.n, U, V); idx = np.nonzero(m)[0]
        from howard_fast import min_cycle
        mu, cyc = min_cycle(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
        lam = Fr(int(W[cyc].sum()), len(cyc))
        if a.lam:
            assert Fr(a.lam) <= lam, (a.lam, lam)
            lam = Fr(a.lam)
        P, Q = lam.numerator, lam.denominator
        if a.start:
            from min_range import min_start_potential, init_sums
            Dst, pi = min_start_potential(A, U, V, W, P, Q, 300)
            assert pi is not None, 'no start-bounded potential found'
            pi = pi - pi.min()
            Dst = int((pi - Q * init_sums(A)).max())
        else:
            pi = bellman_ford(A.n, U, V, W, P, Q)
            assert pi is not None
            pi = pi - pi.min()
        vb = None if a.no_vb else vertex_bound(A, U, V, W)
        del U, V, W, EXT
    else:
        import lean_minimize as LM
        from lean_automaton import LeanAutomaton
        A = LeanAutomaton(L, k, K)
        G = LM.Graph(A, set(keys))
        print(f'graph: {A.n} states, {G.E} edges ({time.time() - T0:.0f}s, peak {LM.rss_mb()} MB)', flush=True)
        lam = G.min_mean()
        if a.lam:
            assert Fr(a.lam) <= lam, (a.lam, lam)
            lam = Fr(a.lam)
        P, Q = lam.numerator, lam.denominator
        if a.start:
            Dst, pi = LM.min_start_potential(A, G, P, Q, 300)
            assert pi is not None, 'no start-bounded potential found'
            pi -= pi.min()
            Dst = LM.start_constant(A, pi, Q)
        else:
            pi = LM.bellman_ford(G, P, Q)
            assert pi is not None
            pi -= pi.min()
        R0 = int(pi.max())
        FW = choose_width(R0)
        FH = 1 << (FW - 1)
        if not fits(FW, R0):
            # the potential of smallest start constant has too large a range for the fields: cap
            # the range (Bellman-Ford from min(cap, D + Q * symbol sum)); D grows a little
            cap = min(FH - P, FH - 1 - NS * Q)
            print(f'range {R0} does not fit {FW}-bit fields; capping the potential at {cap}', flush=True)
            lib = LM._load(); digs = LM.init_digs(A)
            if a.start:
                lo, hi, best = -Q * int(digs.max()), 300, None
                while lo <= hi:
                    mid = (lo + hi) // 2
                    if mid + Q * int(digs.min()) < 0:
                        lo = mid + 1; continue
                    pc = np.empty(A.n, np.int32)
                    for s_ in range(len(A.shapes)):
                        pc[s_ * A.m1:(s_ + 1) * A.m1] = np.minimum(cap, mid + Q * digs)
                    pc = LM.bf(G, P, Q, pc, 4000, 1)
                    ok = pc is not None and lib.check_pot(G.n, G.starts, G.V, G.W, P, Q, pc, 1, int(mid), digs, A.m1) == 0
                    if ok:
                        best = (mid, pc); hi = mid - 1
                    else:
                        lo = mid + 1
                    pc = None
                assert best is not None, ('no start-bounded potential of range <= cap', cap)
                pi = best[1]; pi -= pi.min()
                Dst = LM.start_constant(A, pi, Q)
            else:
                pc = LM.bf(G, P, Q, np.full(A.n, cap, np.int32), 4000, 1)
                assert pc is not None, ('no potential of range <= cap', cap)
                pi = pc; pi -= pi.min()
            print(f'capped potential: range {int(pi.max())}' + (f', start constant {Dst}' if a.start else ''), flush=True)
        # the potential is re-checked on every edge of the graph (C), then by the mirrors below
        assert LM._load().check_pot(G.n, G.starts, G.V, G.W, P, Q, pi, 0, 0, LM.init_digs(A), A.m1) == 0
        vb = None if a.no_vb else LM.vertex_bound(A, G)
        G = None
        print(f'potential done ({time.time() - T0:.0f}s, peak {LM.rss_mb()} MB)', flush=True)
    R = int(pi.max())
    if a.graph == 'fast':
        FW = choose_width(R)
    # field width FW: top bit FT, half HALF = 2^(FW-1) (the carry bit of the comparison), largest
    # stored value FM = HALF - 1, full-field mask FF, base FB = 2^FW
    FT = FW - 1; FH = 1 << FT; FM = FH - 1; FF = (1 << FW) - 1; FB = 1 << FW
    FDT = np.dtype('<u1') if FW == 8 else np.dtype('<u2')
    B3 = FW * N3; B2 = FW * N2
    if FW == 16:
        S = S + '16'
        CODE = f'code{S}'
        POS = f'pos{S}'
        REPL = f'pack_tab_rep{S}'
    group = a.group or (12 if FW == 8 else 4)

    def wfile(name):
        return W16File(os.path.join(OUT, name)) if FW == 16 else open(os.path.join(OUT, name), 'w')
    # next-state field P + pot <= HALF, current-state field Q * s + pot < HALF
    assert fits(FW, R), (f'fields do not fit {FW} bits; try --lam with a smaller denominator or --width 16', P, Q, R)
    shapes = A.shapes
    split = a.split == 'yes' or (a.split == 'auto' and len(shapes) * NS ** (k - 1) > 1 << 22)
    assert FW == 8 or split, '16-bit fields are implemented for the split layout only (use --split yes)'
    if a.start:
        C = P * L - Q * (L - k) + Dst
        Dpos, Dneg = max(Dst, 0), max(-Dst, 0)
        # start table fields: Dpos + Q * (symbol sum) where that fits 8 bits; otherwise (and always
        # in --split chains) min(127, Dpos + Q * symbol sum): pot + Dneg <= the clipped value is a
        # stronger statement, so any Q works as long as R + Dneg <= 127
        sclip = split or not (Q * NS * (k - 1) + Dpos < FH)
        if sclip:
            assert R + Dneg <= FM, ('start check: R + Dneg must stay below the field half', R, Dneg, FH)
        else:
            assert Q * NS * (k - 1) + Dpos < 128 and R + Dneg <= 128, ('start table does not fit 8 bits', Q, Dst, R)
    else:
        C = P * L - Q * (L - 1) + R
    assert C >= 0
    B = (9179 * Q + C - 8 * Q) // (P + 35 * Q)
    print(f'lambda {lam} range {R} dp-bound {None if vb is None else vb - 1} edges, potential-bound {B} edges'
          + (f' (start constant D = {Dst})' if a.start else '') + (' [split layout]' if split else ''), flush=True)

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

    def pos_np(z):
        return N3 * (z // N3) + N2 * (z % NS) + (z // NS) % N2

    def tsize(cc):
        """fields of the table of `cc` centres (two-centre tables carry copies up to N3 fields)"""
        return max(NS ** cc, N3)

    # natural tables (bool over codes, newest symbol least significant), forward and reversed
    revcode = {}
    for cc in range(2, k + 1):
        x = np.arange(NS ** cc, dtype=np.int64); r = np.zeros_like(x)
        for j in range(cc):
            r = r * NS + (x // NS ** j) % NS
        revcode[cc] = r
    fwdT, revT = {}, {}
    for dirs, alpha in keys:
        cc = len(alpha); w = ws[shape_code(dirs)]
        cs = sym_codes(alpha, NS, K)
        fwdT.setdefault((cc, w), np.zeros(NS ** cc, bool))[cs] = True
        revT.setdefault((cc, w), np.zeros(NS ** cc, bool))[revcode[cc][cs]] = True

    def spread_fields(Tb, cc):
        """fields (byte indices) whose top bit the spread table sets"""
        z = np.flatnonzero(Tb)
        if cc == 2:
            return np.sort((N2 * (z % NS) + (z // NS))[:, None] + NS * np.arange(NS)[None, :], axis=None)
        return np.sort(pos_np(z))

    def spread_bytes(Tb, cc):
        out = np.zeros(tsize(cc), FDT)
        out[spread_fields(Tb, cc)] = FH
        return out
    M1 = NS ** (k - 1)
    F = NS ** k                                            # fields of the full comparison
    # potentials: natural order (field y = state code y), pos layout, block-replicated layout
    potv = [np.minimum(R, pi[i * M1:(i + 1) * M1]).astype(FDT) for i in range(len(shapes))]
    posM1 = pos_np(np.arange(M1))
    idxR = (N2 * (np.arange(F) // N3) + np.arange(F) % N2)

    def potT_bytes(i):
        out = np.empty(M1, FDT); out[posM1] = potv[i]; return out

    def potR_bytes(i):
        return potv[i][idxR]

    def to_int(arr):
        return int.from_bytes(np.ascontiguousarray(arr).tobytes(), 'little')
    print(f'tables and potentials ready ({time.time() - T0:.0f}s)', flush=True)

    # ---- Python mirror of the transition inequality (natural codes) --------------
    ncodes = NS ** k; X = np.arange(ncodes, dtype=np.int64)
    Xmod = {cc: (X % (NS ** cc)).astype(np.int32) for cc in range(2, k + 1)}
    Xhi = (X // NS).astype(np.int32); Xlo = (X % M1).astype(np.int32); snew = (X % NS + 1).astype(np.int16)
    exts = []
    for c0 in shapes:
        i0 = sidx[shape_code(c0)]
        for d in range(9):
            c = c0 + (d,)
            if induced(c):
                exts.append((c, i0, sidx[shape_code(tuple(canon(c[1:])))]))
    checked = 0
    for c, i0, i1 in exts:
        blocked = np.zeros(ncodes, bool)
        for cc in range(2, k + 1):
            sub = c[L + 1 - (cc + 1):]
            Fw = ws.get(shape_code(tuple(canon(sub)))); Vv = ws.get(shape_code(tuple(canon(tuple(reversed(sub))))))
            if Fw is not None and (cc, Fw) in fwdT:
                blocked |= fwdT[(cc, Fw)][Xmod[cc]]
            if Vv is not None and (cc, Vv) in revT:
                blocked |= revT[(cc, Vv)][Xmod[cc]]
        p0 = potv[i0][Xhi].astype(np.int32); p1 = potv[i1][Xlo].astype(np.int32)
        ok = blocked | (Q * snew + p0 >= P + p1)
        assert ok.all(), (c,)
        checked += int((~blocked).sum())
    for c in rgs(L + 1):
        if induced(c):
            assert c[:L] in shapes and c[L] < 9
    print('python re-check passed on', checked, 'shard transitions', flush=True)
    # mirror of the packed check, field by field, on the stored layouts (what `checkT` compares)
    WPATF = np.tile((np.arange(N3) // N2 + 1).astype(np.int16), F // N3)
    sp_cache = {}

    def sp(name, cc, w):
        key = (name, cc, w)
        if key not in sp_cache:
            tb = (fwdT if name == 'f' else revT).get((cc, w))
            sp_cache[key] = spread_bytes(tb, cc) if tb is not None else np.zeros(tsize(cc), FDT)
        return sp_cache[key]
    pairs = 0
    for c, i0, i1 in exts:
        tabs = {}
        for cc in range(2, k + 1):
            sub = c[L + 1 - (cc + 1):]
            Fw = ws.get(shape_code(tuple(canon(sub)))); Vw = ws.get(shape_code(tuple(canon(tuple(reversed(sub))))))
            tabs[cc] = sp('f', cc, Fw) | sp('r', cc, Vw)
        BL = np.tile(tabs[2] | tabs[3], F // N3)
        for cc in range(4, k):
            BL |= np.tile(tabs[cc], F // NS ** cc)
        BL |= tabs[k]
        Av = P + np.tile(potT_bytes(i1), NS).astype(np.int32)
        Bv = WPATF.astype(np.int32) * Q + potR_bytes(i0).astype(np.int32)
        assert (Av <= FH).all() and (Bv < FH).all()
        assert (((Bv + FH - Av) & FH) | (BL & FH) == FH).all(), ('packed check fails', c)
        pairs += 1
    del Xmod, Xhi, Xlo, snew, X, sp_cache
    print('packed check mirrors', pairs, 'pairs', flush=True)
    ONES = sum(1 << (FW * l) for l in range(N3)); HI = FH * ONES
    WPAT = sum((l // N2 + 1) << (FW * l) for l in range(N3))
    def repk(n, m):
        return sum(1 << (FW * n * j) for j in range(m))
    REPB_INT = repk(N2, NS)
    DEPTH = (M1 // N2 - 1).bit_length()
    if not split:
        # the big-number tables of the single Data module
        sfwd = {key: to_int(spread_bytes(v, key[0])) for key, v in fwdT.items()}
        srev = {key: to_int(spread_bytes(v, key[0])) for key, v in revT.items()}
        potC = {i: to_int(potv[i]) for i in range(len(shapes))}
        potT = {i: to_int(potT_bytes(i)) for i in range(len(shapes))}
        potR = {i: to_int(potR_bytes(i)) for i in range(len(shapes))}
        # mirror of the Lean `spreadR` recursion (divide and conquer over blocks) for every shape
        def spread(Cv, d):
            if d == 0:
                return Cv & ((1 << B2) - 1)
            h = d - 1
            return spread(Cv & ((1 << (B2 << h)) - 1), h) | (spread(Cv >> (B2 << h), h) << (B3 << h))
        for i in potR:
            assert spread(potC[i], DEPTH) * REPB_INT == potR[i], ('spreadR mirror', i)
        print('spreadR mirrors potR for', len(potR), 'shapes', flush=True)
    else:
        # keys of the window tables (the values are written as sparse bit sets)
        sfwd = {key: None for key in fwdT}
        srev = {key: None for key in revT}
        potC = {i: None for i in range(len(shapes))}
        potR = potC

    # ---- Lean text ------------------------------------------------------------
    CHUNK = 8192

    def geo(n, m):
        """Lean text of `repK n m` in closed form (see `repK_eq_div`)."""
        return f'(({FB} ^ ({n} * {m}) - 1) / ({FB} ^ {n} - 1))'

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
        # large values become their own constants, so `unfold name` and `simp` see a short term
        consts, lines = [], [f'def {name} ({var1} {var2} : Nat) : Nat :=']
        for x in sorted(by_a):
            parts = []
            for y, v in sorted(by_a[x].items()):
                t = lit(v)
                if len(t) > 64:
                    consts.append(f'def {name}v{x}_{y} : Nat := {t}')
                    t = f'{name}v{x}_{y}'
                parts.append(f'if {var2} = {y} then {t}')
            lines.append(f'  if {var1} = {x} then ({' else '.join(parts)} else 0) else')
        lines.append('  0')
        return '\n'.join(consts + lines)

    def chain1e(name, var, exprs):
        lines = [f'def {name} ({var} : Nat) : Nat :=']
        for x, e in sorted(exprs.items()):
            lines.append(f'  if {var} = {x} then {e} else')
        lines.append('  0')
        return '\n'.join(lines)

    def chain1(name, var, table):
        consts, lines = [], [f'def {name} ({var} : Nat) : Nat :=']
        for x, v in sorted(table.items()):
            t = lit(v)
            if len(t) > 64:
                consts.append(f'def {name}v{x} : Nat := {t}')
                t = f'{name}v{x}'
            lines.append(f'  if {var} = {x} then {t} else')
        lines.append('  0')
        return '\n'.join(consts + lines)

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
            lt_thms.append(f'theorem {name}{S}_lt_{cc}_{w} : {name}{S} {cc} {w} < 2 ^ {FW * tsize(cc)} := by decide +kernel')
        cases = ''.join(f'''  by_cases hw{w} : w = {w}
  · subst hw{w}; exact {name}{S}_lt_{cc}_{w}
''' for w in ws_c)
        hyps = ', '.join(f'hw{w}' for w in ws_c)
        return f'''theorem {name}{S}_lt{cc} (w : Nat) : {name}{S} {cc} w < 2 ^ {FW * tsize(cc)} := by
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
                rep_thms.append(f'''theorem {name}{S}_rep_{w} : allBelowR {N3} (fun l => Nat.testBit ({name}{S} 2 {w}) ({FW} * l + {FT}) == Nat.testBit ({name}{S} 2 {w}) ({FW} * ({N2} * (l / {N2}) + l % {NS}) + {FT})) = true := by
  decide +kernel''')
    def rep_universal(name, tbl):
        ws2 = [w for w in w2 if (2, w) in tbl]
        cases = ''.join(f'''  by_cases hw{w} : w = {w}
  · subst hw{w}; exact eq_of_beq (allBelowR_spec _ _ {name}{S}_rep_{w} l hl)
''' for w in ws2)
        hyps = ', '.join(f'hw{w}' for w in ws2)
        return f'''theorem {name}{S}_rep (w : Nat) : ∀ l, l < {N3} →
    Nat.testBit ({name}{S} 2 w) ({FW} * l + {FT}) = Nat.testBit ({name}{S} 2 w) ({FW} * ({N2} * (l / {N2}) + l % {NS}) + {FT}) := by
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
            pot_thms.append(f'theorem {nm}{S}_bnd_{i} (y : Nat) (hy : y < {M1}) : digit ({nm}{S} {i}) y + {FM - R} < {FH} :=\n'
                            f'  bytes_lt_of_masks _ _ _ _ _ hiP{S}_eq onesP{S}_eq (by decide) (by decide +kernel) y hy')
        # layout consistency, block by block: both {N3}-field windows are forced to numerals first,
        # so the inner loop divides small numbers only
        pot_thms.append(f'theorem potT{S}_cons_{i} : consT{S} (potT{S} {i}) (potC{S} {i}) = true := by decide +kernel')
        pot_thms.append(f'theorem potT{S}_lt_{i} : potT{S} {i} < {FB} ^ {M1} := by decide +kernel')
        pot_thms.append(f'theorem potR{S}_lt_{i} : potR{S} {i} < {FB} ^ {F} := by decide +kernel')
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
    potT_lt = f'''theorem potT{S}_lt (i : Nat) : potT{S} i < {FB} ^ {M1} := by
{by_shape(f'potT{S}', lambda i: f'exact potT{S}_lt_{i}', f'rw [h0]; exact Nat.pow_pos (by decide)')}'''
    potR_lt = f'''theorem potR{S}_lt (i : Nat) : potR{S} i < {FB} ^ {F} := by
{by_shape(f'potR{S}', lambda i: f'exact potR{S}_lt_{i}', f'rw [h0]; exact Nat.pow_pos (by decide)')}'''
    potR_eq = f'''theorem potR{S}_digit (i hb l : Nat) (hh : hb < {M1 // N2}) (hl : l < {N3}) :
    digit (potR{S} i) ({N3} * hb + l) = digit (potC{S} i) ({N2} * hb + l % {N2}) := by
{by_shape(f'potR{S}', lambda i: f'exact consR{S}_spec _ _ potR{S}_cons_{i} hb l hh hl', f'''have h0c : potC{S} i = 0 := by
    unfold potC{S}
    simp [{', '.join(f'hi{i}' for i in range(len(shapes)))}]
  rw [h0, h0c]; simp [digit]''')}'''
    # ---- spec lemma text
    bits = [f'Nat.testBit (blk T2 R2) ({FW} * {POS} (code % {N2}) + {FT})'] + \
        [f'Nat.testBit (blk T{cc} R{cc}) ({FW} * {POS} (code % {NS ** cc}) + {FT})' for cc in range(3, k + 1)]
    bool_or = bits[0]
    for bb in bits[1:]:
        bool_or = f'({bool_or} || {bb})'
    conclusion = (f'{bool_or} = true ∨\n      {P} + digit PT1 ({N3} * (code / {N3} % {NS ** (k - 4)}) + {POS} (code % {N3})) ≤ '
                  f'{Q} * (code % {NS} + 1) + digit PC0 (code / {NS})')
    # bits of the replicated window tables
    ew_haves = ''.join(f'''  have ew{cc} : Nat.testBit (blk T{cc} R{cc} * rep{cc}{S}) ({FW} * f + {FT})
      = Nat.testBit (blk T{cc} R{cc}) ({FW} * {POS} (code % {NS ** cc}) + {FT}) := by
    rw [rep{cc}{S}_eq, testBit_mul_rep _ {NS ** cc} {NS ** (k - cc)} _ h{cc} (by omega)]
    have ps := {POS}_split code {NS ** (cc - 3)} (by decide)
    rw [show {N3} * {NS ** (cc - 3)} = {NS ** cc} by rfl] at ps
    have hidx : {FW} * (f % {NS ** cc}) + {FT} = {FW} * {POS} (code % {NS ** cc}) + {FT} := by rw [ps]; omega
    rw [hidx]
''' for cc in range(4, k))
    ew_names = ''.join(f', ew{cc}' for cc in range(4, k))
    ek = f'''  have ew{k} : Nat.testBit (blk T{k} R{k}) ({FW} * f + {FT}) = Nat.testBit (blk T{k} R{k}) ({FW} * {POS} (code % {NS ** k}) + {FT}) := by
    have ps := {POS}_split code {NS ** (k - 3)} (by decide)
    rw [show {N3} * {NS ** (k - 3)} = {NS ** k} by rfl] at ps
    have hidx : {FW} * f + {FT} = {FW} * {POS} (code % {NS ** k}) + {FT} := by rw [ps]; omega
    rw [hidx]
'''
    hlt_hyps = f'    (h3 : blk T2 R2 ||| blk T3 R3 < 2 ^ {FW * N3})' + ''.join(
        f' (h{cc} : blk T{cc} R{cc} < 2 ^ {FW * NS ** cc})' for cc in range(4, k))
    spec = f'''/-- The packed check implies the transition inequality for every code (abstract tables). -/
theorem checkT{S}_spec ({' '.join(argn)} PC0 : Nat) (hc : checkT{S} {' '.join(argn)} = true)
    (code : Nat) (hcode : code < {F})
    (hb0 : ∀ y, y < {M1} → digit PC0 y ≤ {R}) (hb1 : ∀ y, y < {M1} → digit PT1 y ≤ {R})
    (hT : PT1 < {FB} ^ {M1}) (hRl : PR0 < {FB} ^ {F})
    (hR : ∀ hb l, hb < {M1 // N2} → l < {N3} → digit PR0 ({N3} * hb + l) = digit PC0 ({N2} * hb + l % {N2}))
    (h2f : ∀ l, l < {N3} → Nat.testBit T2 ({FW} * l + {FT}) = Nat.testBit T2 ({FW} * ({N2} * (l / {N2}) + l % {NS}) + {FT}))
    (h2r : ∀ l, l < {N3} → Nat.testBit R2 ({FW} * l + {FT}) = Nat.testBit R2 ({FW} * ({N2} * (l / {N2}) + l % {NS}) + {FT}))
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
  have e23 : Nat.testBit ((blk T2 R2 ||| blk T3 R3) * rep3{S}) ({FW} * f + {FT})
      = (Nat.testBit (blk T2 R2) ({FW} * {POS} (code % {N2}) + {FT}) || Nat.testBit (blk T3 R3) ({FW} * {POS} (code % {N3}) + {FT})) := by
    rw [rep3{S}_eq, testBit_mul_rep _ {N3} {NS ** (k - 3)} _ h3 (by omega), show f % {N3} = {POS} (code % {N3}) by omega, Nat.testBit_or]
    have e2' : Nat.testBit (blk T2 R2) ({FW} * {POS} (code % {N3}) + {FT}) = Nat.testBit (blk T2 R2) ({FW} * {POS} (code % {N2}) + {FT}) := by
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
    start_block = ''
    if a.start:
        yy = np.arange(M1)
        symsum_np = sum((yy // NS ** j) % NS + 1 for j in range(k - 1))
        sinit_np = Dpos + Q * symsum_np
        if sclip:
            sinit_np = np.minimum(FM, sinit_np)
        assert sinit_np.max() < FH
        for i in range(len(shapes)):                     # mirror of the start check
            assert (potv[i].astype(np.int64) + Dneg <= sinit_np).all(), ('start bound', i)
        SINIT = to_int(sinit_np.astype(FDT))
        SV = f'min {FM} ({Dpos} + {Q} * symsum{S} ({N3} * h + l))' if sclip else f'{Dpos} + {Q} * symsum{S} ({N3} * h + l)'
        SD = f'min {FM} ({Dpos} + {Q} * symsum{S} y)' if sclip else f'{Dpos} + {Q} * symsum{S} y'
        SDdoc = f'min {FM} ({Dpos} + {Q} * symsum y)' if sclip else f'{Dpos} + {Q} * symsum y'
    if a.start and not split:
        terms = ' + '.join(f'(y % {NS} + 1)' if j == 0 else f'(y / {NS ** j} % {NS} + 1)' for j in range(k - 1))
        start_thms = []
        for i in range(len(shapes)):
            start_thms.append(f'theorem potC{S}_lt_{i} : potC{S} {i} < {FB} ^ {M1} := by decide +kernel')
            start_thms.append(f'theorem potC{S}_start_{i} : swarOK (potC{S} {i} + {Dneg} * onesP{S}) sinit{S} 0 hiP{S} = true := by decide +kernel')
        start_case = lambda i: (f'have h := field_le_of_swarOK {M1} _ _ _ _ {Dneg} potC{S}_lt_{i} sinit{S}_lt hiP{S}_eq onesP{S}_eq '
                                f'(fun y hy => by have := potC{S}_digit_le {i} y hy; omega) '
                                f'(fun y hy => by rw [sinit{S}_digit y hy]; have := symsum{S}_le y; omega) potC{S}_start_{i} y hy; '
                                f'rw [sinit{S}_digit y hy] at h; ' + ('omega' if sclip else 'exact h'))
        start_block = f'''
/-! ### Start states: `pot + {Dneg} <= {Dpos} + {Q} * (sum of the state's symbols)` -/

/-- Sum of the {k - 1} symbols (base-{NS} digits plus one) of a state code. -/
def symsum{S} (y : Nat) : Nat := {terms}

theorem symsum{S}_le (y : Nat) : symsum{S} y ≤ {(k - 1) * NS} := by unfold symsum{S}; omega
theorem symsum{S}_ge (y : Nat) : {k - 1} ≤ symsum{S} y := by unfold symsum{S}; omega

/-- Field `y` holds `{SDdoc}`. -/
def sinit{S} : Nat := {lit(SINIT)}

def sinitOK{S} : Bool :=
  allBelowR {M1 // N3} fun h =>
    letN (winT sinit{S} ({B3} * h) {B3} + 1) fun Wd =>
    allBelowR {N3} fun l => Nat.beq (digit Wd l) ({SV})

theorem sinitOK{S}_eq : sinitOK{S} = true := by decide +kernel
theorem sinit{S}_lt : sinit{S} < {FB} ^ {M1} := by decide +kernel

theorem sinit{S}_digit (y : Nat) (hy : y < {M1}) : digit sinit{S} y = {SD} := by
  have h := sinitOK{S}_eq
  unfold sinitOK{S} at h
  have h1 := allBelowR_spec _ _ h (y / {N3}) (by omega)
  rw [letN_succ] at h1
  have h2 := Nat.eq_of_beq_eq_true (allBelowR_spec _ _ h1 (y % {N3}) (by omega))
  rw [show {B3} * (y / {N3}) = {FW} * ({N3} * (y / {N3})) by omega, show ({B3} : Nat) = {FW} * {N3} by rfl,
    digit_winT _ _ _ _ (by omega)] at h2
  rw [show {N3} * (y / {N3}) + y % {N3} = y by omega] at h2
  exact h2

{chr(10).join(start_thms)}

theorem potC{S}_start (i y : Nat) (hy : y < {M1}) : digit (potC{S} i) y + {Dneg} ≤ {Dpos} + {Q} * symsum{S} y := by
{by_shape(f'potC{S}', start_case, f'rw [h0]; have := symsum{S}_ge y; simp only [digit, Nat.zero_div, Nat.zero_mod]; omega')}
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
    if split:
        potR_def = ''
    elif a.potr == 'computed':
        potR_def = chain1e(f'potR{S}', 'i', {i: f'spreadR{S} (potC{S} {i})' for i in potR})
    elif a.potr == 'blocks':
        # potR = (the N2-field blocks of potC placed N3 fields apart) * (1 + 256^N2 + ... ), the
        # blocks written as one list of B2-bit numerals folded at B3-bit stride: NS times less
        # text than the numeral itself; potR_cons still checks the result against potC
        consts, body = [], [f'def potR{S} (i : Nat) : Nat :=']
        for i in sorted(potR):
            blocks = [(potC[i] >> (B2 * h)) & ((1 << B2) - 1) for h in range(M1 // N2)]
            while blocks and blocks[-1] == 0:
                blocks.pop()
            assert sum(b << (B3 * h) for h, b in enumerate(blocks)) * REPB_INT == potR[i], ('potR blocks', i)
            consts.append(f'def potR{S}v{i} : Nat := ofChunksW {B3} [{", ".join(map(str, blocks))}] * {geo(N2, NS)}')
            body.append(f'  if i = {i} then potR{S}v{i} else')
        body.append('  0')
        potR_def = '\n'.join(consts + body)
    else:
        potR_def = chain1(f'potR{S}', 'i', potR)
    if NS == 8 and a.transpose == 'swap':
        # the mask equalities: 8-bit fields evaluate `repK` by its recursion (as before); 16-bit fields
        # through the closed form `repK_eq_div` (the recursion keeps 512 numbers of 4 Mbit: > 2 GB)
        SWE = 'by decide +kernel' if FW == 8 else 'by\n  rw [repK_eq_div _ _ (by decide)]; decide +kernel'
        consT_block = f'''/-- `T` holds the fields of `C` at the positions `{POS} y`: six delta swaps map `C` to `T`
(`WindowAutomatonTranspose`), one kernel equality of big numbers per shape. -/
def consT{S} (T C : Nat) : Bool := Nat.beq T (trans8 (512 * {M1 // 512}) C)

theorem swMask{S}_e1 : swMask 0 3 (512 * {M1 // 512}) = pack (tab (fun z => if swP 0 3 z then {FF} else 0) 512) * repK 512 {M1 // 512} := {SWE}
theorem swMask{S}_e2 : swMask 3 6 (512 * {M1 // 512}) = pack (tab (fun z => if swP 3 6 z then {FF} else 0) 512) * repK 512 {M1 // 512} := {SWE}
theorem swMask{S}_e3 : swMask 1 4 (512 * {M1 // 512}) = pack (tab (fun z => if swP 1 4 z then {FF} else 0) 512) * repK 512 {M1 // 512} := {SWE}
theorem swMask{S}_e4 : swMask 4 7 (512 * {M1 // 512}) = pack (tab (fun z => if swP 4 7 z then {FF} else 0) 512) * repK 512 {M1 // 512} := {SWE}
theorem swMask{S}_e5 : swMask 2 5 (512 * {M1 // 512}) = pack (tab (fun z => if swP 2 5 z then {FF} else 0) 512) * repK 512 {M1 // 512} := {SWE}
theorem swMask{S}_e6 : swMask 5 8 (512 * {M1 // 512}) = pack (tab (fun z => if swP 5 8 z then {FF} else 0) 512) * repK 512 {M1 // 512} := {SWE}
theorem swMask{S}_d1 : swMask 0 3 (512 * {M1 // 512}) &&& (swMask 0 3 (512 * {M1 // 512}) <<< ({FW} * 7)) = 0 := by decide +kernel
theorem swMask{S}_d2 : swMask 3 6 (512 * {M1 // 512}) &&& (swMask 3 6 (512 * {M1 // 512}) <<< ({FW} * 56)) = 0 := by decide +kernel
theorem swMask{S}_d3 : swMask 1 4 (512 * {M1 // 512}) &&& (swMask 1 4 (512 * {M1 // 512}) <<< ({FW} * 14)) = 0 := by decide +kernel
theorem swMask{S}_d4 : swMask 4 7 (512 * {M1 // 512}) &&& (swMask 4 7 (512 * {M1 // 512}) <<< ({FW} * 112)) = 0 := by decide +kernel
theorem swMask{S}_d5 : swMask 2 5 (512 * {M1 // 512}) &&& (swMask 2 5 (512 * {M1 // 512}) <<< ({FW} * 28)) = 0 := by decide +kernel
theorem swMask{S}_d6 : swMask 5 8 (512 * {M1 // 512}) &&& (swMask 5 8 (512 * {M1 // 512}) <<< ({FW} * 224)) = 0 := by decide +kernel

theorem consT{S}_spec (T C : Nat) (h : consT{S} T C = true) (y : Nat) (hy : y < {M1}) :
    digit T ({POS} y) = digit C y := by
  unfold consT{S} at h
  rw [Nat.eq_of_beq_eq_true h]
  exact digit_trans8 {M1 // 512} C y (by omega) swMask{S}_e1 swMask{S}_e2 swMask{S}_e3 swMask{S}_e4 swMask{S}_e5 swMask{S}_e6
    swMask{S}_d1 swMask{S}_d2 swMask{S}_d3 swMask{S}_d4 swMask{S}_d5 swMask{S}_d6'''
    else:
        consT_block = f'''/-- `T` holds the fields of `C` at the positions `{POS} y`, checked block by block on numerals. -/
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
  rw [show {B3} * (y / {N3}) = {FW} * ({N3} * (y / {N3})) by omega, show ({B3} : Nat) = {FW} * {N3} by rfl,
    digit_winT _ _ _ _ (by omega), digit_winT _ _ _ _ (by omega)] at h2
  rw [show {N3} * (y / {N3}) + y % {N3} = y by omega] at h2
  rw [← h2]
  congr 1
  unfold {POS}
  omega'''
    data = '' if split else f'''/-
Generated by milestones/10-window-aggregate/scripts/gen_lean_swar.py.  Do not edit.
L = {L} directions of memory, k = {k} (windows of 2..{k} centres), radius {"/".join(RL)},
{len(keys)} exclusions (source: {source}), lambda = {P}/{Q}, potential range {R} on {A.n} states.
Word-parallel kernel check: see the header of gen_lean_swar.py and WindowAutomatonSwar.lean.
-/
import WindowAutomatonDefs
import WindowAutomatonLoop
import WindowAutomatonSwar{chr(10) + 'import WindowAutomatonSym' if NS != 6 else ''}{chr(10) + 'import WindowAutomatonTranspose' if NS == 8 and a.transpose == 'swap' else ''}

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000
-- the tables are large numerals; elaborating them is slow but involves no search
set_option maxHeartbeats 0
{pos_block}
{ifchain(f'shapeIdx{S}', sidx, len(shapes))}

{ifchain(f'wshapeIdx{S}', ws, len(wshapes))}

/-- Excluded patterns of window shape `w` with `c` centres: bit `{FW} * pos z + {FT}` for code `z`
(two-centre tables carry the {['', '', '', '', '', '', 'six', 'seven', 'eight', 'nine'][NS]} copies of each entry that a {N3}-field block needs). -/
{chain2(f'sfwd{S}', 'c', 'w', sfwd)}

/-- The same for windows whose reversed direction list has shape `w` (symbols reversed). -/
{chain2(f'srev{S}', 'c', 'w', srev)}

/-- Potential of shape `i`: 8-bit field `y` for the natural code `y` of the {k - 1} counts. -/
{chain1(f'potC{S}', 'i', potC)}

/-- The same potentials stored at `pos y`. -/
{chain1(f'potT{S}', 'i', potT)}

/-- Every {N2}-field block of `C` moved to the start of its own {N3}-field block and repeated {NS}
times there (field `{N3} h + l` holds field `{N2} h + l % {N2}` of `C`).  Divide and conquer over
the blocks (each half forced to a numeral by `letNat`), so the kernel's work grows with the
logarithm of the number of blocks; `potR_cons` checks the result against `potC` for every shape. -/
def spreadR{S} (C : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat) (fun C => C &&& (2 ^ {B2} - 1))
    (fun d rec C => letNat (C + 1) fun C =>
      rec (C &&& (2 ^ ({B2} * 2 ^ d) - 1)) ||| (rec (C >>> ({B2} * 2 ^ d)) <<< ({B3} * 2 ^ d)))
    {(M1 // N2 - 1).bit_length()} C) * {geo(N2, NS)}

/-- The potentials with every {N2}-field block repeated {NS} times (field `{N3} h + l` holds
field `{N2} h + l % {N2}` of `potC`). -/
{potR_def}

def {CODE} : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => {CODE} l (acc * {NS} + (s - 1))

def wsh{S} (ds : List Nat) : Nat := wshapeIdx{S} (shapeCode (canon ds))
def sh{S} (ds : List Nat) : Nat := shapeIdx{S} (shapeCode (canon ds))

/-- Is the window (directions `ds`, symbols `syms`) excluded, in either orientation? -/
def wforb{S} (ds syms : List Nat) : Bool :=
  Nat.testBit (blk (sfwd{S} syms.length (wsh{S} ds)) (srev{S} syms.length (wsh{S} ds.reverse))) ({FW} * {POS} ({CODE} syms 0) + {FT})

/-- Potential of a state. -/
def pot{S} (h t : List Nat) : Nat := clip {R} (digit (potC{S} (sh{S} h)) ({CODE} t 0))

theorem pot{S}_le (h t : List Nat) : pot{S} h t ≤ {R} := clip_le _ _

def ones{S} : Nat := {ONES}
def hi{S} : Nat := {HI}
def wpat{S} : Nat := {WPAT}
-- replicated constants as closed forms of the geometric sums `repK` (`repK_eq_div`): the kernel
-- computes them with one power and one division instead of reading megabytes of numerals
def onesP{S} : Nat := ones{S} * {geo(N3, M1 // N3)}
def hiP{S} : Nat := hi{S} * {geo(N3, M1 // N3)}
def onesF{S} : Nat := ones{S} * {geo(N3, F // N3)}
def hiF{S} : Nat := hi{S} * {geo(N3, F // N3)}
def wpatF{S} : Nat := wpat{S} * {geo(N3, F // N3)}
def repB{S} : Nat := {geo(N2, NS)}
def repA{S} : Nat := {geo(M1, NS)}
{chr(10).join(f'def rep{cc}{S} : Nat := {geo(NS ** cc, NS ** (k - cc))}' for cc in range(3, k))}
theorem ones{S}_eq : ones{S} = pack (tab (fun _ => 1) {N3}) := by decide +kernel
theorem hi{S}_eq : hi{S} = pack (tab (fun _ => {FH}) {N3}) := by decide +kernel
theorem wpat{S}_eq : wpat{S} = pack (tab (fun l => l / {N2} + 1) {N3}) := by decide +kernel
theorem onesF{S}_eq : onesF{S} = pack (tab (fun _ => 1) {F}) := by
  have h := pack_tab_rep (fun _ => 1) {N3} {F // N3}
  rw [← ones{S}_eq] at h
  have e : onesF{S} = ones{S} * repK {N3} {F // N3} := by rw [repK_eq_div _ _ (by decide)]; rfl
  rw [e]; exact h.symm
theorem hiF{S}_eq : hiF{S} = pack (tab (fun _ => 128) {F}) := by
  have h := pack_tab_rep (fun _ => 128) {N3} {F // N3}
  rw [← hi{S}_eq] at h
  have e : hiF{S} = hi{S} * repK {N3} {F // N3} := by rw [repK_eq_div _ _ (by decide)]; rfl
  rw [e]; exact h.symm
theorem wpatF{S}_eq : wpatF{S} = pack (tab (fun l => l % {N3} / {N2} + 1) {F}) := by
  have h := pack_tab_rep (fun l => l / {N2} + 1) {N3} {F // N3}
  rw [← wpat{S}_eq] at h
  have e : wpatF{S} = wpat{S} * repK {N3} {F // N3} := by rw [repK_eq_div _ _ (by decide)]; rfl
  rw [e]; exact h.symm
theorem repB{S}_eq : repB{S} = repK {N2} {NS} := (repK_eq_div _ _ (by decide)).symm
theorem repA{S}_eq : repA{S} = repK {M1} {NS} := (repK_eq_div _ _ (by decide)).symm
{chr(10).join(f'theorem rep{cc}{S}_eq : rep{cc}{S} = repK {NS ** cc} {NS ** (k - cc)} := (repK_eq_div _ _ (by decide)).symm' for cc in range(3, k))}
theorem onesP{S}_eq : onesP{S} = pack (tab (fun _ => 1) {M1}) := by
  have h := pack_tab_rep (fun _ => 1) {N3} {M1 // N3}
  rw [← ones{S}_eq] at h
  have e : onesP{S} = ones{S} * repK {N3} {M1 // N3} := by rw [repK_eq_div _ _ (by decide)]; rfl
  rw [e]; exact h.symm
theorem hiP{S}_eq : hiP{S} = pack (tab (fun _ => 128) {M1}) := by
  have h := pack_tab_rep (fun _ => 128) {N3} {M1 // N3}
  rw [← hi{S}_eq] at h
  have e : hiP{S} = hi{S} * repK {N3} {M1 // N3} := by rw [repK_eq_div _ _ (by decide)]; rfl
  rw [e]; exact h.symm

{consT_block}

/-- `Rt` holds every {N2}-field block of `C` {NS} times in a row (`potR` against `potC`). -/
def consR{S} (Rt C : Nat) : Bool :=
  allBelowR {M1 // N2} fun h => Nat.beq (winT Rt ({B3} * h) {B3}) (winT C ({B2} * h) {B2} * repB{S})

theorem consR{S}_spec (Rt C : Nat) (h : consR{S} Rt C = true) (hb l : Nat) (hh : hb < {M1 // N2}) (hl : l < {N3}) :
    digit Rt ({N3} * hb + l) = digit C ({N2} * hb + l % {N2}) := by
  unfold consR{S} at h
  have h1 := Nat.eq_of_beq_eq_true (allBelowR_spec _ _ h hb hh)
  have h2 := congrArg (fun X => digit X l) h1
  simp only at h2
  rw [show {B3} * hb = {FW} * ({N3} * hb) by omega, show ({B3} : Nat) = {FW} * {N3} by rfl, digit_winT _ _ _ _ hl] at h2
  rw [h2]
  unfold winT
  rw [show {B2} * hb = {FW} * ({N2} * hb) by omega, show ({B2} : Nat) = {FW} * {N2} by rfl, winT_pack, repB{S}_eq,
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
{start_block}
/-- Step test for one window of {L + 1} directions. -/
def check{S} (c : List Nat) : Bool :=
  !inducedPattern c || checkT{S}
    {check_args}
    (potR{S} (sh{S} (c.take {L}))) (potT{S} (sh{S} (c.drop 1)))

def shapes{S} : List (List Nat) := {lst(lst(c) for c in shapes)}

end Snake9.WindowAutomaton
'''
    def emit_split():
        """--split: Base (constants, layout checks, start table), Pot<g> (the potentials of `a.group`
        shapes each, as elaboration-time numerals, with their per-shape kernel checks), Tab (window
        tables as sparse bit sets) and Data (dispatch, universal statements, check)."""
        import enc
        assert NS == 8 and a.transpose == 'swap', '--split assumes eight symbols and the delta-swap layout check'
        nsh = len(shapes)
        groups = [list(range(g, min(g + group, nsh))) for g in range(0, nsh, group)]
        hdr = f'''/-
Generated by gen_lean_swar.py (split layout).  Do not edit.
L = {L} directions of memory, k = {k} (windows of 2..{k} centres), radius {"/".join(RL)},
{len(keys)} exclusions (source: {source}), lambda = {P}/{Q}, potential range {R} on {A.n} states.
Large numerals are elaboration-time literals (`nat_lit%`, WindowAutomatonLit): the kernel sees
plain numerals and checks every property used.
-/'''
        opts = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0'
        W16_IMPORTS = '' if FW == 8 else ('\nimport WindowAutomatonSwar16\nimport WindowAutomatonTranspose16'
                                          '\nimport WindowAutomatonConsD16\nimport WindowAutomatonLit16')
        lit_big = lambda name, expr: f'def {name} : Nat := nat_lit% {expr}'
        # ---- start table (block decomposition: symsum (N3 h + l) = symsumH h + symsumL l)
        sstart = ''
        if a.start:
            nh = k - 4                                            # digits of the block index h
            tmin, tmax = nh, nh * NS
            termsH = ' + '.join(f'(h % {NS} + 1)' if j == 0 else f'(h / {NS ** j} % {NS} + 1)' for j in range(nh))
            termsL = ' + '.join(f'(l % {NS} + 1)' if j == 0 else f'(l / {NS ** j} % {NS} + 1)' for j in range(3))
            terms = ' + '.join(f'(y % {NS} + 1)' if j == 0 else f'(y / {NS ** j} % {NS} + 1)' for j in range(k - 1))
            ll = np.arange(N3)
            sl = sum((ll // NS ** j) % NS + 1 for j in range(3))
            sblk = {t: to_int(np.minimum(FM, Dpos + Q * (t + sl)).astype(FDT)) for t in range(tmin, tmax + 1)}
            hh = np.arange(M1 // N3)
            shh = sum((hh // NS ** j) % NS + 1 for j in range(nh))
            for h in range(M1 // N3):                           # mirror: block h of sinit is sblk (symsumH h)
                assert to_int(sinit_np[N3 * h:N3 * (h + 1)].astype(FDT)) == sblk[int(shh[h])]
            sstart = f'''
/-! ### Start states: `pot + {Dneg} <= min {FM} ({Dpos} + {Q} * (sum of the state's symbols))` -/

/-- Sum of the {k - 1} symbols (base-{NS} digits plus one) of a state code. -/
def symsum{S} (y : Nat) : Nat := {terms}
def symsumH{S} (h : Nat) : Nat := {termsH}
def symsumL{S} (l : Nat) : Nat := {termsL}

theorem symsum{S}_le (y : Nat) : symsum{S} y ≤ {(k - 1) * NS} := by unfold symsum{S}; omega
theorem symsum{S}_ge (y : Nat) : {k - 1} ≤ symsum{S} y := by unfold symsum{S}; omega
theorem symsum{S}_split (y : Nat) : symsum{S} y = symsumH{S} (y / {N3}) + symsumL{S} (y % {N3}) := by
  unfold symsum{S} symsumH{S} symsumL{S}; omega
theorem symsumH{S}_ge (h : Nat) : {tmin} ≤ symsumH{S} h := by unfold symsumH{S}; omega
theorem symsumH{S}_le (h : Nat) : symsumH{S} h ≤ {tmax} := by unfold symsumH{S}; omega

/-- Field `y` holds `min {FM} ({Dpos} + {Q} * symsum y)`. -/
{lit_big(f'sinit{S}', f'ofB64 "{enc.b64_of_bytes(sinit_np.astype(FDT).tobytes())}"')}

/-- The {N3}-field block of `sinit` for blocks `h` with `symsumH h = t`. -/
{chain1(f'sblk{S}', 't', sblk)}

def sinitBlkOK{S} : Bool :=
  allBelowR {M1 // N3} fun h => Nat.beq (winT sinit{S} ({B3} * h) {B3}) (sblk{S} (symsumH{S} h))

def sblkOK{S} : Bool :=
  allBelowR {tmax + 1 - tmin} fun u => allBelowR {N3} fun l =>
    Nat.beq (digit (sblk{S} (u + {tmin})) l) (min {FM} ({Dpos} + {Q} * (u + {tmin} + symsumL{S} l)))

theorem sinitBlkOK{S}_eq : sinitBlkOK{S} = true := by decide +kernel
theorem sblkOK{S}_eq : sblkOK{S} = true := by decide +kernel
theorem sinit{S}_lt : sinit{S} < {FB} ^ {M1} := by decide +kernel

theorem sinit{S}_digit (y : Nat) (hy : y < {M1}) : digit sinit{S} y = min {FM} ({Dpos} + {Q} * symsum{S} y) := by
  have h1 := Nat.eq_of_beq_eq_true (allBelowR_spec _ _ sinitBlkOK{S}_eq (y / {N3}) (by omega))
  have h2 := congrArg (fun X => digit X (y % {N3})) h1
  simp only at h2
  rw [show {B3} * (y / {N3}) = {FW} * ({N3} * (y / {N3})) by omega, show ({B3} : Nat) = {FW} * {N3} by rfl,
    digit_winT _ _ _ _ (Nat.mod_lt _ (by decide))] at h2
  rw [show {N3} * (y / {N3}) + y % {N3} = y by omega] at h2
  have hg := symsumH{S}_ge (y / {N3})
  have hl := symsumH{S}_le (y / {N3})
  have h3 := allBelowR_spec _ _ sblkOK{S}_eq (symsumH{S} (y / {N3}) - {tmin}) (by omega)
  have h4 := Nat.eq_of_beq_eq_true (allBelowR_spec _ _ h3 (y % {N3}) (Nat.mod_lt _ (by decide)))
  rw [show symsumH{S} (y / {N3}) - {tmin} + {tmin} = symsumH{S} (y / {N3}) by omega] at h4
  rw [h2, h4, symsum{S}_split]
  all_goals omega
'''
        consR_split = f'''/-- `Rt` holds every {N2}-field block of `C` {NS} times in a row: the divide-and-conquer check `consD`. -/
theorem consR{S}_spec (Rt C : Nat) (h : consD {N2} {N3} (repK {N2} {NS}) {DEPTH} Rt C = true) (hb l : Nat)
    (hh : hb < {M1 // N2}) (hl : l < {N3}) : digit Rt ({N3} * hb + l) = digit C ({N2} * hb + l % {N2}) :=
  consD_spec {N2} {NS} (by decide) {DEPTH} Rt C h hb l (Nat.lt_of_lt_of_le hh (by decide)) hl'''
        def rep_eq(name, n, m):
            return f'theorem {name}_eq : {name} = repK {n} {m} := by rw [repK_eq_div _ _ (by decide)]; decide +kernel'
        def pack_eq(name, base, val, n):
            return f'''theorem {name}_eq : {name} = pack (tab ({val}) {n}) := by
  have h := pack_tab_rep ({val.replace('fun l => l % ' + str(N3) + ' / ', 'fun l => l / ')}) {N3} {n // N3}
  rw [← {base}_eq] at h
  have e : {name} = {base} * repK {N3} {n // N3} := by rw [repK_eq_div _ _ (by decide)]; decide +kernel
  rw [e]; exact h.symm'''
        base = f'''{hdr}
import WindowAutomatonDefs
import WindowAutomatonLoop
import WindowAutomatonSwar
import WindowAutomatonSym
import WindowAutomatonTranspose
import WindowAutomatonConsD
import WindowAutomatonLit{W16_IMPORTS}

namespace Snake9.WindowAutomaton

{opts}
{pos_block}
{ifchain(f'shapeIdx{S}', sidx, len(shapes))}

{ifchain(f'wshapeIdx{S}', ws, len(wshapes))}

def {CODE} : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => {CODE} l (acc * {NS} + (s - 1))

def wsh{S} (ds : List Nat) : Nat := wshapeIdx{S} (shapeCode (canon ds))
def sh{S} (ds : List Nat) : Nat := shapeIdx{S} (shapeCode (canon ds))

def ones{S} : Nat := {ONES}
def hi{S} : Nat := {HI}
def wpat{S} : Nat := {WPAT}
-- replicated constants: numerals computed at elaboration (`nat_lit%`), checked against the
-- geometric sums `repK` once below; the shard checks read them without recomputing
{lit_big(f'onesP{S}', f'ones{S} * {geo(N3, M1 // N3)}')}
{lit_big(f'hiP{S}', f'hi{S} * {geo(N3, M1 // N3)}')}
{lit_big(f'onesF{S}', f'ones{S} * {geo(N3, F // N3)}')}
{lit_big(f'hiF{S}', f'hi{S} * {geo(N3, F // N3)}')}
{lit_big(f'wpatF{S}', f'wpat{S} * {geo(N3, F // N3)}')}
def repB{S} : Nat := {geo(N2, NS)}
{lit_big(f'repA{S}', geo(M1, NS))}
{chr(10).join(lit_big(f'rep{cc}{S}', geo(NS ** cc, NS ** (k - cc))) for cc in range(3, k))}
theorem ones{S}_eq : ones{S} = pack (tab (fun _ => 1) {N3}) := by decide +kernel
theorem hi{S}_eq : hi{S} = pack (tab (fun _ => {FH}) {N3}) := by decide +kernel
theorem wpat{S}_eq : wpat{S} = pack (tab (fun l => l / {N2} + 1) {N3}) := by decide +kernel
{pack_eq(f'onesF{S}', f'ones{S}', 'fun _ => 1', F)}
{pack_eq(f'hiF{S}', f'hi{S}', f'fun _ => {FH}', F)}
{pack_eq(f'wpatF{S}', f'wpat{S}', f'fun l => l % {N3} / {N2} + 1', F)}
{pack_eq(f'onesP{S}', f'ones{S}', 'fun _ => 1', M1)}
{pack_eq(f'hiP{S}', f'hi{S}', f'fun _ => {FH}', M1)}
theorem repB{S}_eq : repB{S} = repK {N2} {NS} := (repK_eq_div _ _ (by decide)).symm
{rep_eq(f'repA{S}', M1, NS)}
{chr(10).join(rep_eq(f'rep{cc}{S}', NS ** cc, NS ** (k - cc)) for cc in range(3, k))}

{consT_block}

{consR_split}

/-- All {NS ** k} symbol codes at once: the next-state table repeated {NS} times, the
block-replicated current-state table, and the window tables replicated to {F} fields,
compared field-wise in one step. -/
def checkT{S} ({' '.join(argn)} : Nat) : Bool :=
  swarOK (PT1 * repA{S} + {P} * onesF{S}) ({Q} * wpatF{S} + PR0) ({blmask}) hiF{S}
{sstart}
end Snake9.WindowAutomaton
'''
        wfile(f'WindowAutomaton{S}Base.lean').write(base)
        # ---- potentials, one module per group of shapes
        for g, grp in enumerate(groups):
            body = []
            for i in grp:
                body.append(lit_big(f'potC{S}v{i}', f'ofB64 "{enc.b64_of_bytes(potv[i].tobytes())}"'))
                body.append(lit_big(f'potT{S}v{i}', f'trans8 (512 * {M1 // 512}) potC{S}v{i}'))
                body.append(lit_big(f'potR{S}v{i}', f'spreadBlocks potC{S}v{i} {N2} {N3} 0 {M1 // N2} * repB{S}'))
                for nm in ('potC', 'potT'):
                    body.append(f'theorem {nm}{S}_bnd_{i} (y : Nat) (hy : y < {M1}) : digit {nm}{S}v{i} y + {FM - R} < {FH} :=\n'
                                f'  bytes_lt_of_masks _ _ _ _ _ hiP{S}_eq onesP{S}_eq (by decide) (by decide +kernel) y hy')
                body.append(f'theorem potT{S}_cons_{i} : consT{S} potT{S}v{i} potC{S}v{i} = true := by decide +kernel')
                body.append(f'theorem potT{S}_lt_{i} : potT{S}v{i} < {FB} ^ {M1} := by decide +kernel')
                body.append(f'theorem potR{S}_lt_{i} : potR{S}v{i} < {FB} ^ {F} := by decide +kernel')
                body.append(f'theorem potR{S}_cons_{i} : consD {N2} {N3} (repK {N2} {NS}) {DEPTH} potR{S}v{i} potC{S}v{i} = true := by\n  decide +kernel')
                if a.start:
                    body.append(f'theorem potC{S}_lt_{i} : potC{S}v{i} < {FB} ^ {M1} := by decide +kernel')
                    body.append(f'theorem potC{S}_start_{i} : swarOK (potC{S}v{i} + {Dneg} * onesP{S}) sinit{S} 0 hiP{S} = true := by decide +kernel')
            wfile(f'WindowAutomaton{S}Pot{g}.lean').write(f'''{hdr}
import WindowAutomaton{S}Base

namespace Snake9.WindowAutomaton

{opts}

/-! Shapes {grp[0]}..{grp[-1]}: potential in code order (`potC`), at `pos y` (`potT`, by the delta swaps)
and block-replicated (`potR`); the numerals are computed while elaborating and checked below. -/

{chr(10).join(body)}

end Snake9.WindowAutomaton
''')
        # ---- window tables
        def tab_text(Tb, cc):
            f = spread_fields(Tb, cc)
            if len(f) == 0:
                return '0'
            v_bits = FW * f + FT
            if tsize(cc) * FW <= CHUNK:
                return str(sum(1 << int(b) for b in v_bits))
            return f'nat_lit% ofGaps "{enc.gaps_of_positions(v_bits)}"'
        def chain2s(name, var1, var2, tbls):
            by_a = {}
            for (x, y), tb in tbls.items():
                by_a.setdefault(x, {})[y] = tab_text(tb, x)
            consts, lines = [], [f'def {name} ({var1} {var2} : Nat) : Nat :=']
            for x in sorted(by_a):
                parts = []
                for y, t in sorted(by_a[x].items()):
                    if len(t) > 64:
                        consts.append(f'def {name}v{x}_{y} : Nat := {t}')
                        t = f'{name}v{x}_{y}'
                    parts.append(f'if {var2} = {y} then {t}')
                lines.append(f'  if {var1} = {x} then ({' else '.join(parts)} else 0) else')
            lines.append('  0')
            return '\n'.join(consts + lines)
        wfile(f'WindowAutomaton{S}Tab.lean').write(f'''{hdr}
import WindowAutomaton{S}Base

namespace Snake9.WindowAutomaton

{opts}

/-- Excluded patterns of window shape `w` with `c` centres: bit `{FW} * pos z + {FT}` for code `z`
(two-centre tables carry the eight copies of each entry that a {N3}-field block needs). -/
{chain2s(f'sfwd{S}', 'c', 'w', fwdT)}

/-- The same for windows whose reversed direction list has shape `w` (symbols reversed). -/
{chain2s(f'srev{S}', 'c', 'w', revT)}

{chr(10).join(rep_thms)}

{rep_universal('sfwd', sfwd)}

{rep_universal('srev', srev)}

{chr(10).join(lt_thms)}

{chr(10).join(lt_univ)}

end Snake9.WindowAutomaton
''')
        # ---- Data: dispatch and the universal statements
        def disp(nm):
            return '\n'.join([f'def {nm}{S} (i : Nat) : Nat :='] + [f'  if i = {i} then {nm}{S}v{i} else' for i in range(nsh)] + ['  0'])
        at_thms = '\n'.join(f'theorem {nm}{S}_at_{i} : {nm}{S} {i} = {nm}{S}v{i} := rfl' for i in range(nsh) for nm in ('potC', 'potT', 'potR'))
        potC_le_s = f'''theorem potC{S}_digit_le (i y : Nat) (hy : y < {M1}) : digit (potC{S} i) y ≤ {R} := by
{by_shape(f'potC{S}', lambda i: f'rw [potC{S}_at_{i}]; have h := potC{S}_bnd_{i} y hy; omega', f'rw [h0]; simp [digit]')}'''
        potT_le_s = f'''theorem potT{S}_digit_le (i y : Nat) (hy : y < {M1}) : digit (potT{S} i) y ≤ {R} := by
{by_shape(f'potT{S}', lambda i: f'rw [potT{S}_at_{i}]; have h := potT{S}_bnd_{i} y hy; omega', f'rw [h0]; simp [digit]')}'''
        hyps_all = ', '.join(f'hi{i}' for i in range(nsh))
        potT_eq_s = f'''theorem potT{S}_digit (i y : Nat) (hy : y < {M1}) : digit (potT{S} i) ({POS} y) = digit (potC{S} i) y := by
{by_shape(f'potT{S}', lambda i: f'rw [potT{S}_at_{i}, potC{S}_at_{i}]; exact consT{S}_spec _ _ potT{S}_cons_{i} y hy', f"""have h0c : potC{S} i = 0 := by
    unfold potC{S}
    simp [{hyps_all}]
  rw [h0, h0c]; simp [digit]""")}'''
        potT_lt_s = f'''theorem potT{S}_lt (i : Nat) : potT{S} i < {FB} ^ {M1} := by
{by_shape(f'potT{S}', lambda i: f'rw [potT{S}_at_{i}]; exact potT{S}_lt_{i}', f'rw [h0]; exact Nat.pow_pos (by decide)')}'''
        potR_lt_s = f'''theorem potR{S}_lt (i : Nat) : potR{S} i < {FB} ^ {F} := by
{by_shape(f'potR{S}', lambda i: f'rw [potR{S}_at_{i}]; exact potR{S}_lt_{i}', f'rw [h0]; exact Nat.pow_pos (by decide)')}'''
        potR_eq_s = f'''theorem potR{S}_digit (i hb l : Nat) (hh : hb < {M1 // N2}) (hl : l < {N3}) :
    digit (potR{S} i) ({N3} * hb + l) = digit (potC{S} i) ({N2} * hb + l % {N2}) := by
{by_shape(f'potR{S}', lambda i: f'rw [potR{S}_at_{i}, potC{S}_at_{i}]; exact consR{S}_spec _ _ potR{S}_cons_{i} hb l hh hl', f"""have h0c : potC{S} i = 0 := by
    unfold potC{S}
    simp [{hyps_all}]
  rw [h0, h0c]; simp [digit]""")}'''
        start_s = ''
        if a.start:
            start_case = lambda i: (f'rw [potC{S}_at_{i}]; '
                                    f'have h := field_le_of_swarOK {M1} _ _ _ _ {Dneg} potC{S}_lt_{i} sinit{S}_lt hiP{S}_eq onesP{S}_eq '
                                    f'(fun y hy => by have := potC{S}_bnd_{i} y hy; omega) '
                                    f'(fun y hy => by rw [sinit{S}_digit y hy]; omega) potC{S}_start_{i} y hy; '
                                    f'rw [sinit{S}_digit y hy] at h; omega')
            start_s = f'''theorem potC{S}_start (i y : Nat) (hy : y < {M1}) : digit (potC{S} i) y + {Dneg} ≤ {Dpos} + {Q} * symsum{S} y := by
{by_shape(f'potC{S}', start_case, f'rw [h0]; have := symsum{S}_ge y; simp only [digit, Nat.zero_div, Nat.zero_mod]; omega')}'''
        data_s = f'''{hdr}
{chr(10).join(f'import WindowAutomaton{S}Pot{g}' for g in range(len(groups)))}
import WindowAutomaton{S}Tab

namespace Snake9.WindowAutomaton

{opts}

/-- Potential of shape `i`: {FW}-bit field `y` for the natural code `y` of the {k - 1} counts. -/
{disp('potC')}

/-- The same potentials stored at `pos y`. -/
{disp('potT')}

/-- The potentials with every {N2}-field block repeated {NS} times (field `{N3} h + l` holds
field `{N2} h + l % {N2}` of `potC`). -/
{disp('potR')}

{at_thms}

/-- Is the window (directions `ds`, symbols `syms`) excluded, in either orientation? -/
def wforb{S} (ds syms : List Nat) : Bool :=
  Nat.testBit (blk (sfwd{S} syms.length (wsh{S} ds)) (srev{S} syms.length (wsh{S} ds.reverse))) ({FW} * {POS} ({CODE} syms 0) + {FT})

/-- Potential of a state. -/
def pot{S} (h t : List Nat) : Nat := clip {R} (digit (potC{S} (sh{S} h)) ({CODE} t 0))

theorem pot{S}_le (h t : List Nat) : pot{S} h t ≤ {R} := clip_le _ _

{potC_le_s}

{potT_le_s}

{potT_eq_s}

{potT_lt_s}

{potR_lt_s}

{potR_eq_s}

{start_s}

/-- Step test for one window of {L + 1} directions. -/
def check{S} (c : List Nat) : Bool :=
  !inducedPattern c || checkT{S}
    {check_args}
    (potR{S} (sh{S} (c.take {L}))) (potT{S} (sh{S} (c.drop 1)))

def shapes{S} : List (List Nat) := {lst(lst(c) for c in shapes)}

end Snake9.WindowAutomaton
'''
        wfile(f'WindowAutomaton{S}Data.lean').write(data_s)
        emit_split.modules = [f'WindowAutomaton{S}Base'] + [f'WindowAutomaton{S}Pot{g}' for g in range(len(groups))] + \
            [f'WindowAutomaton{S}Tab']
    emit_split.modules = []
    if split:
        emit_split()
    else:
        wfile(f'WindowAutomaton{S}Data.lean').write(data)
    wfile(f'WindowAutomaton{S}Spec.lean').write(f'''/-
Generated by gen_lean_swar.py: the extraction lemma for the packed check (abstract tables).
-/
import WindowAutomaton{S}Data

namespace Snake9.WindowAutomaton

{spec}
end Snake9.WindowAutomaton
''')
    # ---- shards, table (same scheme as gen_lean_automaton_k.py) --------------
    for i, c in enumerate(shapes):
        wfile(f'WindowAutomaton{S}Shard{i}.lean').write(f"""/-
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
    if split:
        # the RGS enumeration in pieces (one declaration per prefix of all but the last `nrest`
        # labels): one kernel check of all strings keeps every intermediate term (gigabytes at L = 8)
        nrest = 3
        jpre = L + 1 - nrest
        assert jpre <= 8
        def rgs_list(n, m=0):
            if n == 0:
                yield []
                return
            for a0 in range(m + 1):
                for r in rgs_list(n - 1, max(m, a0 + 1)):
                    yield [a0] + r
        pres = list(rgs_list(jpre))
        pre_thms = '\n'.join(f'theorem rgs{S}_p{t} : allRGS {nrest} (rgsBound {lst(p)} 0) (fun l => rgsP{S} ({lst(p)} ++ l)) = true := by\n  decide +kernel'
                             for t, p in enumerate(pres))
        pre_cases = '\n'.join(f'  · exact rgs{S}_p{t}' for t in range(len(pres)))
        wfile(f'WindowAutomaton{S}Table.lean').write(f"""/-
Generated by gen_lean_swar.py (split layout).  Combines the {len(shapes)} shards.
-/
{chr(10).join(f'import WindowAutomaton{S}Shard{i}' for i in range(len(shapes)))}
import WindowAutomatonCode
import WindowAutomatonRGS

namespace Snake9.WindowAutomaton

set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- one declaration at a time: the kernel checks below are large, and checking them in parallel
-- multiplies the memory
set_option Elab.async false

def shapeCodes{S} : List Nat := shapes{S}.map shapeCode

theorem shapes{S}_ok : shapes{S}.all (fun s => s.length == {L} && s.all (· < 8)) = true := by decide

/-- The test every restricted growth string of length {L + 1} must pass: not induced (xor-mask
test, a consequence of `inducedPattern`), or a listed shape followed by a label below nine. -/
def rgsP{S} (c : List Nat) : Bool :=
  !inducedFast c || (shapeCodes{S}.any (Nat.beq (shapeCode (c.take {L}))) && (c.drop {L}).all (· < 9))

/-- The {len(pres)} restricted growth strings of length {jpre}. -/
def rgsPre{S} : List (List Nat) := {lst(lst(p) for p in pres)}

theorem rgsPre{S}_ok : rgsPre{S}.all (fun q => q.length == {jpre} && q.all (· < 8)) = true := by decide +kernel

theorem rgsPre{S}_cov : letN (maskOf shapeCode rgsPre{S} + 1)
    (fun M => allRGS {jpre} 0 (fun pre => Nat.testBit M (shapeCode pre))) = true := by
  decide +kernel

{pre_thms}

theorem rgs{S}_pres : ∀ pre, pre ∈ rgsPre{S} → allRGS {nrest} (rgsBound pre 0) (fun l => rgsP{S} (pre ++ l)) = true := by
  intro pre hpre
  simp only [rgsPre{S}, List.mem_cons, List.not_mem_nil, or_false] at hpre
  rcases hpre with {' | '.join(['rfl'] * len(pres))}
{pre_cases}

theorem check{S}_of_rgs (c : List Nat) (hc : c.length = {L + 1}) (hr : isRGS c 0 = true) :
    check{S} c = true := by
  have hm := allRGS_of_prefixes rgsP{S} {jpre} {nrest} rgsPre{S} rgsPre{S}_ok rgsPre{S}_cov rgs{S}_pres (by decide)
    c (by rw [hc]) hr
  unfold rgsP{S} at hm
  by_cases hind : inducedPattern c = true
  · have hfast := inducedFast_of_inducedPattern c
      (fun d hd => by have := isRGS_bound c 0 hr d hd; omega) hind
    rw [hfast] at hm
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, decide_eq_true_eq] at hm
    obtain ⟨hbit, hlt⟩ := hm
    obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hbit
    obtain ⟨s, hs, hsx⟩ := List.mem_map.mp hx
    have hcode : shapeCode s = shapeCode (c.take {L}) := by rw [hsx]; exact (Nat.eq_of_beq_eq_true hxe).symm
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
    else:
        wfile(f'WindowAutomaton{S}Table.lean').write(f"""/-
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
    # k >= 7 (and --split chains): every omega call on the base-NS code runs in a clean context
    # (helper lemmas below); with seven digits, omega over the whole step context does not finish
    newseq = split or k >= 7
    seq_helpers = ''
    hcode_line = f'have hcode : code < {NS ** k} := by omega'
    potT_hy = '(by omega)'
    clip_hy = ('(by omega)', '(by omega)')
    if newseq:
        av = [f'a{i}' for i in range(1, k + 1)]
        def lin(vs):
            return ' + '.join(f'{v} * {NS ** (len(vs) - 1 - j)}' if j < len(vs) - 1 else v for j, v in enumerate(vs))
        Xk = lin(av)
        conj = [f'({Xk}) % {NS ** cc} = {lin(av[k - cc:])}' for cc in range(k, 1, -1)] + \
            [f'({Xk}) / {NS} = {lin(av[:k - 1])}', f'({Xk}) % {NS} = {av[-1]}', f'{lin(av[:k - 1])} < {M1}', f'{lin(av[1:])} < {M1}']
        dn = [f'd{cc}' for cc in range(k, 1, -1)] + ['d0', 'ds', 'dlo0', 'dlo1']
        bv = [f'b{j}' for j in range(k - 1)]
        dconj = [f'({lin(bv)}) % {NS} = {bv[-1]}'] + [f'({lin(bv)}) / {NS ** j} % {NS} = {bv[k - 2 - j]}' for j in range(1, k - 1)]
        seq_helpers = f"""
/-- Base-{NS} digits of a code (a clean context for omega). -/
theorem code{S}_digits ({' '.join(av)} : Nat) {' '.join(f'(h{v} : {v} < {NS})' for v in av)} :
    {(' ∧' + chr(10) + '    ').join(conj)} := by
  refine ⟨{', '.join(['?_'] * len(conj))}⟩ <;> omega

theorem code{S}_symdigits ({' '.join(bv)} : Nat) {' '.join(f'(h{v} : {v} < {NS})' for v in bv)} :
    {(' ∧' + chr(10) + '    ').join(dconj)} := by
  refine ⟨{', '.join(['?_'] * len(dconj))}⟩ <;> omega
""" + chr(10).join(f"""
theorem code{S}_eq{m} ({' '.join(f'v{j}' for j in range(m))} : Nat) :
    {CODE} {lst(f'v{j}' for j in range(m))} 0 = {code6_of([f'v{j}' for j in range(m)])} := by
  simp only [{CODE}]; omega""" for m in range(2, k + 1))
        if a.start:
            vs_ = [f's{j}' for j in range(k - 1)]
            seq_helpers += f"""

theorem symsum{S}_code ({' '.join(vs_)} : Nat) {' '.join(f'(b{j} : 1 ≤ s{j})' for j in range(k - 1))} {' '.join(f'(c{j} : s{j} ≤ {NS})' for j in range(k - 1))} :
    symsum{S} ({code6_of(vs_)}) = {' + '.join(vs_)} := by
  obtain ⟨{', '.join(f'q{j}' for j in range(k - 1))}⟩ := code{S}_symdigits {' '.join(f'({v} - 1)' for v in vs_)} {' '.join('(by omega)' for _ in vs_)}
  unfold symsum{S}
  rw [{', '.join(f'q{j}' for j in range(k - 1))}]
  clear {' '.join(f'q{j}' for j in range(k - 1))}
  omega
"""
        seq_helpers += '\n\n'
        hcode_line += (f'\n  obtain ⟨{", ".join(dn)}⟩ := code{S}_digits {" ".join(f"({v} - 1)" for v in syms_all)} '
                       + ' '.join('(by omega)' for _ in syms_all) + '\n  '
                       + '\n  '.join([f'have e{cc} : code % {NS ** cc} = {code6_of(syms_all[k - cc:])} := by rw [hcd]; exact d{cc}' for cc in range(k, 1, -1)]
                                      + [f'have e0 : code / {NS} = {code6_of(syms_all[:k - 1])} := by rw [hcd]; exact d0',
                                         f'have es : code % {NS} + 1 = {sym_s} := by rw [hcd, ds]; exact Nat.sub_add_cancel ({GE1("hs")})']))
        digit_rewrites = 'rw [' + ', '.join([f'e{cc}' for cc in range(k, 1, -1)] + ['e0', 'es']) + '] at h'
        code_rewrites = '\n  '.join(
            f'have c{cc} := code{S}_eq{cc} {" ".join(syms_all[k - cc:]) if False else " ".join("(" + v + ")" for v in syms_all[k - cc:])}\n  rw [c{cc}] at hw{cc}'
            for cc in range(2, k + 1)) + '\n  ' + \
            f'have c0 := code{S}_eq{k - 1} {" ".join("(" + v + ")" for v in syms_all[:k - 1])}\n  ' + \
            f'have c1 := code{S}_eq{k - 1} {" ".join("(" + v + ")" for v in syms_all[1:])}'
        potT_hy = '(Nat.mod_lt _ (by decide))'
        clip_hy = ('dlo1', 'dlo0')
    if not a.start:
        sum_total = f"""theorem sumA_ge{S} (a : Nat → Nat) (m : Nat) (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j) :
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
  omega"""
    else:
        st_syms = [f'{SYM} (a (i+{first + j}))' for j in range(k - 1)]
        st_list = lst(st_syms)
        st_hyps = ' '.join(f'(h{j} : 1 ≤ a (i+{first + j}))' for j in range(k - 1))
        st_bounds = '\n  '.join(f'have hb{j} : 1 ≤ {SYM} (a (i+{first + j})) := {GE1(f"h{j}")}\n  '
                                 f'have hc{j} : {SYM} (a (i+{first + j})) ≤ {NS} := {LEK}' for j in range(k - 1))
        prefix = ' + '.join(f'a {j}' for j in range(1, first)) if first > 1 else '0'
        symlist = ' + '.join(f'{SYM} (a {first + j})' for j in range(k - 1))
        sym0 = [f'{SYM} (a {first + j})' for j in range(k - 1)]
        pos_prefix = '\n'.join(f'  have hp{j} := hpos {j} (by omega) (by omega)' for j in range(1, first))
        st_args = ' '.join(f'(hpos ({first + j}) (by omega) (by omega))' for j in range(k - 1))
        le_list = '\n'.join(f'    have := {LE} (a {first + j})' for j in range(k - 1))
        vs = [f's{j}' for j in range(k - 1)]
        v_hyps = ' '.join(f'(b{j} : 1 ≤ s{j})' for j in range(k - 1)) + ' ' + ' '.join(f'(c{j} : s{j} ≤ {NS})' for j in range(k - 1))
        v_code = code6_of(vs)
        v_sum = ' + '.join(vs)
        h3_proof = (f'symsum{S}_code {" ".join(vs)} {" ".join(f"b{j}" for j in range(k - 1))} {" ".join(f"c{j}" for j in range(k - 1))}'
                    if newseq else f'by unfold symsum{S}; omega')
        st_ge = ' '.join(f'({GE1(f"h{j}")})' for j in range(k - 1))
        st_le = ' '.join(f'({LEK})' for j in range(k - 1))
        sum_total = f"""/-- The start state's potential is bounded by its own symbols (plain variables keep the
arithmetic small: every big table term is generalized away before omega). -/
theorem pot{S}_start (h : List Nat) ({' '.join(vs)} : Nat) {v_hyps} :
    pot{S} h {lst(vs)} + {Dneg} ≤ {Dpos} + {Q} * ({v_sum}) := by
  have hs : {CODE} {lst(vs)} 0 = {v_code} := by simp only [{CODE}]; omega
  have h3 : symsum{S} ({v_code}) = {v_sum} := {h3_proof}
  unfold pot{S}
  rw [hs]
  generalize hy : {v_code} = y at h3 ⊢
  have h1 := potC{S}_start (sh{S} h) y (by omega)
  have h2 := clip_le_self {R} (digit (potC{S} (sh{S} h)) y)
  generalize digit (potC{S} (sh{S} h)) y = z at h1 h2 ⊢
  generalize clip {R} z = w at h2 ⊢
  omega

theorem Φ{S}_start (d a : Nat → Nat) (i : Nat) {st_hyps} :
    Φ{S} d a i + {Dneg} ≤ {Dpos} + {Q} * ({' + '.join(st_syms)}) :=
  pot{S}_start _ {' '.join('_' for _ in vs)} {st_ge} {st_le}

theorem sumA_ge{S} (a : Nat → Nat) (m : Nat) (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j) :
    ∀ n, n + {L} ≤ m → {prefix} + ({symlist}) + S{S} a n ≤ sumA a (n + {L - 1})
  | 0, h => by
    simp only [S{S}, sumA, Nat.zero_add, Nat.reduceAdd]
{le_list}
    omega
  | n + 1, h => by
    have ih := sumA_ge{S} a m hpos n (by omega)
    have := {LE} (a (n+{L}))
    show {prefix} + ({symlist}) + (S{S} a n + {SYM} (a (n+{L}))) ≤ sumA a (n+{L - 1}) + a (n+{L - 1}+1)
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
  have h0 := Φ{S}_start d a 0 {st_args}
  simp only [Nat.zero_add] at h0
{pos_prefix}
  have he : m - {L} + {L - 1} = m - 1 := by omega
  rw [he] at hsum
  omega
"""
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

{seq_helpers}theorem step{S}_raw (x : List Nat) (hx : x.length = {L + 1}) ({tvars} s : Nat)
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
  {hcode_line}
  have h := checkT{S}_spec {' '.join(['_'] * (2 * (k - 1) + 2))} (potC{S} (sh{S} (x.take {L}))) hc code hcode
    (fun y hy => potC{S}_digit_le _ y hy) (fun y hy => potT{S}_digit_le _ y hy) (potT{S}_lt _) (potR{S}_lt _)
    (fun hb l hh hl => potR{S}_digit _ hb l hh hl) (sfwd{S}_rep _) (srev{S}_rep _)
    (Nat.or_lt_two_pow (Nat.or_lt_two_pow (sfwd{S}_lt2 _) (srev{S}_lt2 _)) (Nat.or_lt_two_pow (sfwd{S}_lt3 _) (srev{S}_lt3 _)))
    {' '.join(f'(Nat.or_lt_two_pow (sfwd{S}_lt{cc} _) (srev{S}_lt{cc} _))' for cc in range(4, k))}
  have e1 : {N3} * (code / {N3} % {NS ** (k - 4)}) + {POS} (code % {N3}) = {POS} (code % {M1}) := by
    have ps := {POS}_split code {NS ** (k - 4)} (by decide)
    rw [show {N3} * {NS ** (k - 4)} = {M1} by rfl] at ps
    exact ps.symm
  rw [e1, potT{S}_digit _ _ {potT_hy}] at h
  unfold wforb{S} at {hw_names}
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at {hw_names}
  {code_rewrites}
  {digit_rewrites}
  rw [{', '.join(f'hw{cc}' for cc in range(2, k + 1))}] at h
  simp only [Bool.false_or, Bool.false_eq_true, false_or] at h
  unfold pot{S}
  rw [c0, c1]
  rw [clip_eq_of_le _ _ (potC{S}_digit_le _ _ {clip_hy[0]}), clip_eq_of_le _ _ (potC{S}_digit_le _ _ {clip_hy[1]})]
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

{sum_total}
end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.total_bound{S}
"""
    wfile(f'WindowAutomaton{S}Sequence.lean').write(seq)
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
({len(keys)} certified exclusions, radius {"/".join(RL)}).  The premise is NOT proved in Lean; the
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
    wfile(f'AggregateDirection{S}Conditional.lean').write(wrapper)
    mods = ['WindowAutomatonLoop', 'WindowAutomatonSwar', 'WindowAutomatonCode'] + (['WindowAutomatonSym'] if NS != 6 else []) + \
        (['WindowAutomatonTranspose', 'WindowAutomatonConsD', 'WindowAutomatonLit', 'WindowAutomatonRGS'] if split else []) + \
        (['WindowAutomatonSwar16', 'WindowAutomatonTranspose16', 'WindowAutomatonConsD16', 'WindowAutomatonLit16'] if FW == 16 else []) + emit_split.modules + \
        [f'WindowAutomaton{S}Data', f'WindowAutomaton{S}Spec'] + \
        [f'WindowAutomaton{S}Shard{i}' for i in range(len(shapes))] + \
        [f'WindowAutomaton{S}Table', f'WindowAutomaton{S}Sequence', f'AggregateDirection{S}Conditional']
    json.dump({'suffix': S, 'L': L, 'k': k, 'K': K, 'radius': a.radius, 'lambda': str(lam), 'range': R,
               'bound_edges': B, 'dp_bound_edges': None if vb is None else vb - 1, 'exclusions': len(keys), 'states': A.n,
               'shapes': len(shapes), 'modules': mods, 'kernel_check': 'swar', 'field_bits': FW, 'potential_group': group,
               'theorem': f'Snake9.upper_{B}_of_direction_windows{S}'},
              open(a.json_out or os.path.join(DATA_DIR, f'lean_chain_{S}.json'), 'w'), indent=1)
    print('wrote', len(mods), 'modules; theorem', f'upper_{B}_of_direction_windows{S}', 'w2 shapes', w2)


if __name__ == '__main__':
    main()
