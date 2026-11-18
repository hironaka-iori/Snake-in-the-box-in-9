#!/usr/bin/env python3
"""Generated Lean modules of the 230 assembly (milestone 37): the K7 cover tables, the per-shape row
checks, the glue chunks and the top module.

    c230gen.py --out DIR [--chunk 250] [--rows-per-module 6] [--only-shapes N,...]

Inputs (all committed): lean435/data/c230derive.json.gz (c230derive.py: the 58,817 exclusions of the
chain with their certificate source), milestones/37-230-feasibility/data/c230share.json.gz (the 132
corner-share keys), the 231 plan and its free-key derivations (lean435/data/freederive_*), and the
chain's tables (decoded from the 4.19 source of WindowAutomatonK7R34C7W16Tab.lean, for the Python-side
pre-check only; the Lean checks read the chain's own definitions).

Spec layer (rebuilt by the auditor):
  C230KeysP<g>   key interval lists `ks<i>_<k>` (chunks) and shapes `sh<i>`; core stack only
  C230Keys       `tab230 : List Entry` = [(sh<i>, ks<i>), ...], `ks<i> = ks<i>_0 ++ ks<i>_1 ++ ...`
  C230Rows<n>_<p> per canonical induced shape s of n directions: `good : GoodT tab230 s` from two
                 kernel row checks (`rowCheck`, `C230K7.fwdOK_of` / `revOK_of`, or the empty-row forms)
  C230Shapes     shape lists `shapes<n>`, `ShapesCover` (kernel RGS enumeration), `AllGood` per length
Glue (imports certificate interfaces privately):
  G230_<i>_<k>   `AllRB sh<i> ks<i>_<k>`: per key `V….refuted` (230 plan) or
                 `Families.refuted_sub (mkPerm v) s <231 term> (by decide +kernel)`
  G230S          the 132 corner-share keys `RefutedShare (winOf s) [(1, 21)] x 7 12 29`
  G230           `allTab230 : AllTab tab230`, `allShare230 : AllShare230`
Spec modules are written to DIR/spec, glue modules to DIR/glue; also DIR/glue-needs.json (certificate
modules per glue module) and DIR/modules.json.
"""
import argparse, gzip, json, os, pickle, re, sys, itertools, collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.dont_write_bytecode = True
for d in ('milestones/33-233-lean/certify', 'milestones/35-231-lean/scripts', 'milestones/35-231-lean/certify'):
    sys.path.insert(0, os.path.join(ROOT, d))
sys.path.insert(0, HERE)

DERIVE = os.path.join(ROOT, 'lean435', 'data', 'c230derive.json.gz')
SHAREPLAN = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'c230share.json.gz')
PLAN231 = os.path.join(ROOT, 'milestones', '28-combined-identities', 'data', 'certplan231_563_1_cap.json.gz')
FREEDERIVE231 = os.path.join(ROOT, 'lean435', 'data', 'freederive_certplan231_563_1_cap.json.gz')


def lst(x):
    return '[' + ', '.join(str(int(v)) for v in x) + ']'


def blst(b):
    return '[' + ', '.join('(%d, %d)' % (lo, hi) for lo, hi in b) + ']'


def canon(ds):
    m = {}
    return tuple(m.setdefault(x, len(m)) for x in ds)


def shape_code(l):
    a = 1
    for x in l:
        a = a * 8 + x
    return a


def rgs(n):
    def go(pre, m):
        if len(pre) == n:
            yield tuple(pre)
            return
        for a in range(m + 1):
            yield from go(pre + [a], max(m, a + 1))
    yield from go([], 0)


def induced_fast(ds):
    """WindowAutomatonCode.inducedFast: every contiguous block has a nonzero xor mask, and blocks of two or
    more steps a mask that is not a power of two."""
    n = len(ds)
    for i in range(n):
        x = 0
        for j in range(i, n):
            x ^= 1 << ds[j]
            if x == 0 or (j > i and (x & (x - 1)) == 0):
                return False
    return True


def pos(z):
    return 512 * (z // 512) + 64 * (z % 8) + (z // 8) % 64


def code(t):
    a = 0
    for s in t:
        a = a * 8 + (s - 1)
    return a


def qpos(t):
    return 16 * pos(code(t)) + 15


def sym_ok(s, b):
    lo, hi = b
    return (1 <= s <= 7 and lo <= s <= hi) or (s == 8 and lo <= 8 and 21 <= hi)


def box_pts(bs):
    return itertools.product(*[[s for s in range(9) if sym_ok(s, b)] for b in bs])


# ------------------------------------------------------------------ 231 terms (glue435.plain_term)
class Terms231:
    def __init__(self):
        import cert233 as C
        import gen_lean_automaton6sc as GEN
        self.C = C
        P = GEN.load_plan(PLAN231)
        self.P = P
        self.rows = {(tuple(r['key'][0]), tuple(r['key'][1])): r for r in P['plain_rows']}
        self.der = {}
        for k, v in json.load(gzip.open(FREEDERIVE231, 'rt')).items():
            d, s = k.split('|')
            self.der[(tuple(int(x) for x in d.split()), tuple(int(x) for x in s.split()))] = v
        self.pl233 = C.load_plan(C.PLAN)

    def term(self, k):
        C, P, rows, der = self.C, self.P, self.rows, self.der
        r = rows.get(k)
        if r is None or not r['free'] or k in P['h8']:
            if r is not None and r['free'] and k not in P['h8']:
                raise SystemExit(f'free key without derivation {k}')
            n = C.pname(k)
            return f'{n}.refuted', n
        e = der[k]
        if e[0] == 'self':
            n = C.pname(k)
            return f'{n}.refuted', n
        if e[0] == 'seed':
            n = C.pname(k)
            wide = self.pl233[k][1]
            if [tuple(x) for x in wide] == [tuple(x) for x in C.GC.dir_bounds(k[1])]:
                return f'{n}.refuted', n
            return f'(Families.refuted_key_of_wide {n}.refuted (by decide +kernel))', n
        _, seed, meth, v, s = e
        sk = (tuple(seed[0]), tuple(seed[1]))
        n = C.pname(sk)
        if meth == 'L1':
            return f'(Families.refuted_key_of_wide {n}.refuted (by decide +kernel))', n
        return f'(Families.refuted_key_sub (mkPerm {lst(v)}) {s} {n}.refuted (by decide +kernel))', n


HDR = ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--chunk', type=int, default=250, help='keys per glue chunk')
    ap.add_argument('--keys-per-module', type=int, default=6000)
    ap.add_argument('--rows-per-module', type=int, default=4, help='shapes per row module (7-centre rows)')
    ap.add_argument('--tab', default=None, help='pickle of c230tabs.py (decoded chain rows) for the Python pre-check')
    a = ap.parse_args()
    O = a.out
    os.makedirs(O, exist_ok=True)
    D = json.load(gzip.open(DERIVE))['exclusions']
    # ---- table entries: shapes in order (length, code), keys in file order
    by = collections.OrderedDict()
    for e in sorted(D, key=lambda e: (len(e['dirs']), shape_code(e['dirs']))):
        by.setdefault(tuple(e['dirs']), []).append(e)
    shapes_e = list(by)
    idx = {s: i for i, s in enumerate(shapes_e)}
    chunks = {}                          # i -> list of key lists
    for i, s in enumerate(shapes_e):
        es = by[s]
        chunks[i] = [es[j:j + a.chunk] for j in range(0, len(es), a.chunk)]
    mods = collections.OrderedDict()     # module -> dict(layer, imports)

    for sub in ('spec', 'glue'):
        os.makedirs(os.path.join(O, sub), exist_ok=True)

    def write(mod, lines, layer, imports):
        # spec modules go to OUT/spec (rebuilt from source with the chain), glue modules to OUT/glue
        # (compiled from certificate interfaces by assemble230.py)
        open(os.path.join(O, layer, mod + '.lean'), 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
        mods[mod] = dict(layer=layer, imports=imports)

    # ---- keys modules
    parts, cur, size = [], [], 0
    for i in range(len(shapes_e)):
        n = len(by[shapes_e[i]])
        if cur and size + n > a.keys_per_module:
            parts.append(cur)
            cur, size = [], 0
        cur.append(i)
        size += n
    parts.append(cur)
    where = {}
    for g, ids in enumerate(parts):
        L = ['module', '', 'public import C230Cover', '', '@[expose] public section', '',
             f'/-! Keys of the K7 cover, part {g} (lean435/tools/c230gen.py). -/', ''] + HDR + \
            ['namespace Snake9.C230', '']
        for i in ids:
            where[i] = f'C230KeysP{g}'
            L.append(f'def sh{i} : List Nat := {lst(shapes_e[i])}')
            for k, ch in enumerate(chunks[i]):
                L.append(f'def ks{i}_{k} : List (List (Nat × Nat)) := [' + ', '.join(blst(e['alpha']) for e in ch) + ']')
            names = [f'ks{i}_{k}' for k in range(len(chunks[i]))]
            body = names[-1]
            for nm in reversed(names[:-1]):
                body = f'{nm} ++ ({body})' if body != names[-1] else f'{nm} ++ {body}'
            L.append(f'def ks{i} : List (List (Nat × Nat)) := {body}')
            L.append('')
        L += ['end Snake9.C230']
        write(f'C230KeysP{g}', L, 'spec', ['C230Cover'])
    L = ['module', ''] + [f'public import C230KeysP{g}' for g in range(len(parts))] + \
        ['', '@[expose] public section', '', '/-! The key table of the K7 cover (lean435/tools/c230gen.py). -/', ''] + HDR + \
        ['namespace Snake9.C230', '',
         f'/-- The {len(shapes_e)} shapes of the chain\'s tables with their {len(D)} key intervals. -/',
         'def tab230 : List Entry := [' + ', '.join(f'(sh{i}, ks{i})' for i in range(len(shapes_e))) + ']', '',
         'end Snake9.C230']
    write('C230Keys', L, 'spec', [f'C230KeysP{g}' for g in range(len(parts))])

    # ---- shapes of every length, rows
    V2 = 0
    for x in range(1, 9):
        for y in range(1, 9):
            V2 |= 1 << qpos((x, y))
    pre = None
    if a.tab:
        pre = pickle.load(open(a.tab, 'rb'))     # (rows, widx) of c230tabs.py
    shapes_n = {n: [s for s in rgs(n) if induced_fast(s)] for n in range(3, 9)}
    row_mods = []
    for n in range(3, 9):
        c = n - 1
        dep = 0 if c <= 3 else 3 * c - 9
        sl = shapes_n[n]
        per = a.rows_per_module if c == 7 else (12 if c == 6 else 1000)
        for p0 in range(0, len(sl), per):
            mod = f'C230Rows{n}_{p0 // per}'
            L = ['module', '', 'public import C230K7', 'public import C230Keys', '', '@[expose] public section', '',
                 f'/-! Row checks of the K7 cover: shapes of {n} directions, part {p0 // per} (lean435/tools/c230gen.py). -/', '',
                 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option Elab.async false', '',
                 'namespace Snake9.C230', 'open Snake9.WindowAutomaton', '']
            for q, s in enumerate(sl[p0:p0 + per]):
                t = f'{n}_{p0 + q}'
                S = lst(s)
                sr = canon(s[::-1])
                f_i, r_i = idx.get(tuple(s)), idx.get(sr)
                if pre is not None:
                    rows, widx = pre
                    w, wr = widx.get(shape_code(s)), widx.get(shape_code(sr))
                    for kind, ww, ii, rv in (('sfwd', w, f_i, False), ('srev', wr, r_i, True)):
                        T = set(rows.get((kind, c, ww), [])) if ww is not None else set()
                        if c == 2:
                            T = {b for b in T if V2 >> b & 1}
                        M = set()
                        if ii is not None:
                            for e in by[shapes_e[ii]]:
                                for tt in box_pts(e['alpha']):
                                    M.add(qpos(tt[::-1] if rv else tt))
                        assert T <= M, (s, kind, len(T - M))
                        assert ii is not None or not T, (s, kind)
                mask = ' &&& v2' if c == 2 else ''
                if f_i is None:
                    L.append(f'theorem rowF{t} : sfwdK7R34C7W16 {c} (wshK7R34C7W16 {S}) = 0 := by decide +kernel')
                    hf = f'fwdOK_zero rowF{t}'
                else:
                    L.append(f'theorem rowF{t} : rowCheck qpos {c} {dep} (sfwdK7R34C7W16 {c} (wshK7R34C7W16 {S}){mask}) '
                             f'(tab230.getD {f_i} ([], [])).2 = true := by decide +kernel')
                    hf = (f'fwdOK_of_mask (i := {f_i}) (by decide +kernel) (by decide +kernel) v2_ok rowF{t}' if c == 2 else
                          f'fwdOK_of (i := {f_i}) (by decide +kernel) (by decide +kernel) rowF{t}')
                if r_i is None:
                    L.append(f'theorem rowR{t} : srevK7R34C7W16 {c} (wshK7R34C7W16 {S}.reverse) = 0 := by decide +kernel')
                    hr = f'revOK_zero rowR{t}'
                else:
                    L.append(f'theorem rowR{t} : rowCheck qposR {c} {dep} (srevK7R34C7W16 {c} (wshK7R34C7W16 {S}.reverse){mask}) '
                             f'(tab230.getD {r_i} ([], [])).2 = true := by decide +kernel')
                    hr = (f'revOK_of_mask (i := {r_i}) (by decide +kernel) (by decide +kernel) v2_ok rowR{t}' if c == 2 else
                          f'revOK_of (i := {r_i}) (by decide +kernel) (by decide +kernel) rowR{t}')
                L.append(f'theorem good{t} : GoodT tab230 {S} := goodT_of (n := {c}) rfl ({hf}) ({hr})')
                L.append('')
            if n == 3:
                L[L.index('namespace Snake9.C230') + 2:L.index('namespace Snake9.C230') + 2] = [
                    f'/-- The bits `qpos [a, b]` read by `wforb` on two-centre windows. -/',
                    f'def v2 : Nat := {V2}', '',
                    'theorem v2_ok\' : ∀ a, a < 8 → ∀ b, b < 8 → v2.testBit (qpos [a + 1, b + 1]) = true := by decide +kernel',
                    'theorem v2_ok : ∀ a b, a < 8 → b < 8 → v2.testBit (qpos [a + 1, b + 1]) = true :=',
                    '  fun a b ha hb => v2_ok\' a ha b hb', '']
            L.append('end Snake9.C230')
            write(mod, L, 'spec', ['C230K7', 'C230Keys'])
            row_mods.append((mod, n, list(range(p0, min(p0 + per, len(sl))))))
    # ---- shapes module
    L = ['module', '', 'public import C230K7', 'public import C230Keys'] + [f'public import {m}' for m, _, _ in row_mods] + \
        ['', '@[expose] public section', '', '/-! Canonical induced shapes of 3 .. 8 directions, their cover and the per-length '
         '`AllGood` (lean435/tools/c230gen.py). -/', '',
         'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option Elab.async false', '',
         'namespace Snake9.C230', 'open Snake9.WindowAutomaton', '']
    for n in range(3, 9):
        sl = shapes_n[n]
        L.append(f'def shapes{n} : List (List Nat) := [' + ', '.join(lst(s) for s in sl) + ']')
        L.append(f'def coverP{n} (c : List Nat) : Bool := (!inducedFast c || (shapes{n}.map shapeCode).any (Nat.beq (shapeCode c)))')
        L.append(f'theorem shapes{n}_ok : shapes{n}.all (fun s => s.length == {n} && s.all (· < 8)) = true := by decide +kernel')
        if n <= 7:
            L.append(f'theorem cover{n}_all : allRGS {n} 0 coverP{n} = true := by decide +kernel')
            L.append(f'theorem cover{n} : ShapesCover shapes{n} {n} := ⟨shapes{n}_ok, fun c hc hr => allRGS_spec {n} 0 coverP{n} cover{n}_all c hc hr⟩')
        else:
            pres = list(rgs(5))
            L.append('def coverPre8 : List (List Nat) := [' + ', '.join(lst(q) for q in pres) + ']')
            L.append('theorem coverPre8_ok : coverPre8.all (fun q => q.length == 5 && q.all (· < 8)) = true := by decide +kernel')
            L.append('theorem coverPre8_cov : letN (maskOf shapeCode coverPre8 + 1) (fun M => allRGS 5 0 (fun pre => Nat.testBit M (shapeCode pre))) = true := by decide +kernel')
            for k, q in enumerate(pres):
                L.append(f'theorem cover8_p{k} : allRGS 3 (rgsBound {lst(q)} 0) (fun l => coverP8 ({lst(q)} ++ l)) = true := by decide +kernel')
            L.append('theorem cover8_pres : ∀ pre, pre ∈ coverPre8 → allRGS 3 (rgsBound pre 0) (fun l => coverP8 (pre ++ l)) = true := by')
            L.append('  intro pre hpre')
            L.append('  simp only [coverPre8, List.mem_cons, List.not_mem_nil, or_false] at hpre')
            L.append('  rcases hpre with ' + ' | '.join(['rfl'] * len(pres)))
            for k in range(len(pres)):
                L.append(f'  · exact cover8_p{k}')
            L.append('theorem cover8 : ShapesCover shapes8 8 := ⟨shapes8_ok, fun c hc hr => allRGS_of_prefixes coverP8 5 3 coverPre8 '
                     'coverPre8_ok coverPre8_cov cover8_pres (by decide) c (by rw [hc]) hr⟩')
        L.append(f'theorem good{n} : AllGood tab230 shapes{n} := ⟨' + ', '.join(f'good{n}_{i}' for i in range(len(sl))) + ', trivial⟩')
        L.append('')
    L.append('end Snake9.C230')
    write('C230Shapes', L, 'spec', ['C230K7', 'C230Keys'] + [m for m, _, _ in row_mods])

    # ---- glue chunks
    T231 = Terms231()
    needs = {}
    G = []
    for i, s in enumerate(shapes_e):
        for k, ch in enumerate(chunks[i]):
            terms, certs, fam = [], set(), False
            for e in ch:
                if e['src'] == 'plan':
                    m = e['module']
                    terms.append(m.split('.', 1)[1] + '.refuted')
                    certs.add(m)
                else:
                    t, nm = T231.term((tuple(e['key'][0]), tuple(e['key'][1])))
                    certs.add('LocalWindowCert.' + nm)
                    ks = f'Refuted (winOf {lst(e["key"][0])}) (boundsOf {lst(e["key"][1])})'
                    terms.append(f'Families.refuted_sub (mkPerm {lst(e["perm"])}) {e["s"]} ({t} : {ks}) (by decide +kernel)')
                    fam = True
            mod = f'G230_{i}_{k}'
            L = ['module', '', f'public import {where[i]}'] + (['import LocalWindowFamilies'] if fam else []) + \
                [f'import {c}' for c in sorted(certs)] + \
                ['', f'/-! Glue chunk `ks{i}_{k}` of the K7 cover (lean435/tools/c230gen.py). -/', ''] + HDR + \
                ['namespace Snake9.LocalWindow', 'open Snake9.C230', '',
                 f'public theorem glue{i}_{k} : AllRB sh{i} ks{i}_{k} :=',
                 '  ⟨' + ',\n    '.join(terms + ['trivial']) + '⟩', '', 'end Snake9.LocalWindow']
            write(mod, L, 'glue', [where[i]] + (['LocalWindowFamilies'] if fam else []) + sorted(certs))
            needs[mod] = sorted(certs)
            G.append((i, k, mod))
    # ---- share glue
    sp = json.load(gzip.open(SHAREPLAN))['share']
    import c230
    sh_names = [c230.share_name((tuple(r['key'][0]), tuple(r['key'][1]), r['level'] - 1)) for r in sp]
    sh_dirs = [tuple(r['key'][0]) for r in sp]
    assert sorted(sh_dirs) == sorted(shapes_n[8]), 'share shapes differ from the 8-direction shapes'
    L = ['module', '', 'public import C230Shares'] + [f'import LocalWindowCert.{n}' for n in sh_names] + \
        ['', '/-! The 132 corner-share keys of the K7 route (lean435/tools/c230gen.py). -/', ''] + HDR + \
        ['namespace Snake9.LocalWindow', 'open Snake9.C230', '',
         'public theorem glueShare : AllShareL shares230 :=',
         '  ⟨' + ',\n    '.join(f'{n}.refuted' for n in [sh_names[sh_dirs.index(s)] for s in shapes_n[8]]) + ',\n    trivial⟩',
         '', 'end Snake9.LocalWindow']
    write('G230S', L, 'glue', ['C230Shares'] + ['LocalWindowCert.' + n for n in sh_names])
    needs['G230S'] = ['LocalWindowCert.' + n for n in sh_names]
    L = ['module', '', 'public import C230Cover', 'public import LocalWindowShareModel', '', '@[expose] public section', '',
         '/-! The shapes of the 132 corner-share keys, in the order of `shapes8` (lean435/tools/c230gen.py). -/', ''] + HDR + \
        ['namespace Snake9.C230', 'open Snake9.LocalWindow', '',
         'def shares230 : List (List Nat) := [' + ', '.join(lst(s) for s in shapes_n[8]) + ']', '',
         '/-- Every listed 8-direction shape has corner share at least 30 on its 7 centres. -/',
         'def AllShareL : List (List Nat) → Prop',
         '  | [] => True',
         '  | s :: l => RefutedShare (winOf s) [(1, 21), (1, 21), (1, 21), (1, 21), (1, 21), (1, 21), (1, 21)] 12 29 ∧ AllShareL l',
         '',
         'theorem AllShareL.mem : ∀ {L : List (List Nat)}, AllShareL L → ∀ s ∈ L,',
         '    RefutedShare (winOf s) [(1, 21), (1, 21), (1, 21), (1, 21), (1, 21), (1, 21), (1, 21)] 12 29',
         '  | [], _, _, hs => absurd hs List.not_mem_nil',
         '  | _ :: _, ⟨h, hL⟩, s, hs => by',
         '    rcases List.mem_cons.1 hs with rfl | hs',
         '    · exact h',
         '    · exact AllShareL.mem hL s hs', '', 'end Snake9.C230']
    write('C230Shares', L, 'spec', ['C230Cover', 'LocalWindowShareModel'])
    # ---- top glue
    L = ['module', '', 'public import C230Keys', 'public import C230Shares'] + [f'import {m}' for _, _, m in G] + ['import G230S'] + \
        ['', '/-! The certificate premises of the 230 assembly from the glue chunks (lean435/tools/c230gen.py). -/', ''] + HDR + \
        ['namespace Snake9.LocalWindow', 'open Snake9.C230', '']
    ent = []
    for i in range(len(shapes_e)):
        ks = [f'glue{i}_{k}' for k in range(len(chunks[i]))]
        t = ks[-1]
        for g in reversed(ks[:-1]):
            t = f'allRB_append {g} ({t})' if t != ks[-1] else f'allRB_append {g} {t}'
        ent.append(t)
    L += ['public theorem allTab230 : AllTab tab230 :=', '  allTab_of ⟨' + ',\n    '.join(ent + ['trivial']) + '⟩', '',
          'public theorem allShare230 : AllShareL shares230 := glueShare', '', 'end Snake9.LocalWindow']
    write('G230', L, 'glue', ['C230Keys', 'C230Shares'] + [m for _, _, m in G] + ['G230S'])
    json.dump(needs, open(os.path.join(O, 'glue-needs.json'), 'w'), indent=0)
    json.dump(mods, open(os.path.join(O, 'modules.json'), 'w'), indent=0)
    allc = sorted({c for v in needs.values() for c in v})
    print(f'{len(parts)} key modules, {len(row_mods)} row modules, {len(G)} glue chunks + G230S + G230; '
          f'{len(allc)} certificate modules needed; shapes per length ' +
          ', '.join(f'{n}: {len(shapes_n[n])}' for n in range(3, 9)))


if __name__ == '__main__':
    main()
