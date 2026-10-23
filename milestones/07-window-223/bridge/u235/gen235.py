"""Shared per-shape bridge for the 235 bound: one shape CNF, one incremental CaDiCaL session, one
kernel-checked G1 check and a FastRup chain with one target per window.

usage: python3 -I gen235.py WORK OUTDIR DIRS [--setfile F] [--block-hints N] [--module-hints M]

WORK/cuts_<tag>.json : the cycle cuts of the shape (from session.py; untrusted, every cut is a
                       clause the G1 checker re-validates);
writes WORK/<tag>.icnf, runs CaDiCaL 2.1.3 --lidrup (deterministic), trims backwards from the
targets (mtrim), and writes the Lean modules of prefix Q<dirs> to OUTDIR, plus
WORK/<tag>.gen.json (statistics and sha256 of every written module).

Everything emitted is untrusted: the kernel re-checks every RUP step (FastRup), every input clause
against the G1 checker (`S235.check3`) and every window link (`S235.winRef_of`).
"""
import argparse, hashlib, json, os, subprocess, sys, time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.environ.get('REPO', '/home/user/Snake-in-the-box-in-9')
sys.path.insert(0, os.path.join(REPO, 'milestones', '10-window-aggregate', 'scripts'))
sys.path.insert(0, os.path.join(REPO, 'milestones', '07-window-223', 'bridge', 'u239'))
from wincert import Encoding, window_from_dirs
import symsolve

DATA = os.path.join(REPO, 'milestones', '10-window-aggregate', 'data')
CAD = os.environ.get('CADICAL', '/root/.elan/toolchains/leanprover--lean4---v4.19.0/bin/cadical')
MTRIM = os.environ.get('MTRIM', os.path.join(HERE, 'mtrim'))


class Rec(Encoding):
    def atmost(self, lits, k, kind):
        if not hasattr(self, 'blocks'):
            self.blocks = []
        base = self.nv + 1
        super().atmost(lits, k, kind)
        if 0 < k < len(lits):
            assert self.nv == base - 1 + len(lits) * k
            self.blocks.append((base, k, list(lits), kind))


def totalizer(enc, lits, nodes):
    """shapecnf.totalizer, recording every node (base variable, leaf literals)."""
    def rec(ls):
        if len(ls) == 1:
            return [None, ls[0]]
        m = len(ls) // 2
        a, b = rec(ls[:m]), rec(ls[m:])
        p, q = len(a) - 1, len(b) - 1
        o = [None] + [enc.fresh() for _ in range(p + q)]
        nodes.append((o[1], list(ls)))
        assert o[1:] == list(range(o[1], o[1] + p + q))
        for i in range(p + 1):
            for j in range(q + 1):
                if i + j >= 1:
                    enc.add([x for x in ([-a[i]] if i else []) + ([-b[j]] if j else [])] + [o[i + j]], 'tot_up')
                if i + j + 1 <= p + q:
                    enc.add([-o[i + j + 1]] + ([a[i + 1]] if i < p else []) + ([b[j + 1]] if j < q else []), 'tot_down')
        return o
    return rec(lits)


def shape_cnf(dirs, radius, cuts):
    w = window_from_dirs(dirs)
    k = len(dirs) - 1
    enc = Rec(w, [None] * k, radius)
    for c in cuts:
        enc.add_cycle_cut(c)
    VT = enc.nv + 1
    nodes, ge, roots = [], [], []
    X = enc.var
    for i, c in enumerate(w[1:-1], 1):
        used = {(c ^ w[i - 1]).bit_length() - 1, (c ^ w[i + 1]).bit_length() - 1}
        corners = [X[c ^ 1 << a ^ 1 << b] for a, b in combinations(range(9), 2) if a not in used and b not in used]
        assert len(corners) == 21
        ge.append(totalizer(enc, [-x for x in corners], nodes))
        roots.append(len(nodes) - 1)
    VL = enc.nv + 1
    gens = symsolve.lexgens(dirs)
    extra, info, nv = symsolve.lex_clauses(enc, gens, VL)
    for cl in extra:
        enc.add(cl, 'lex')
    enc.nv = nv
    return enc, ge, roots, nodes, VT, VL, info


def cube(ge, alpha):
    A = []
    for i, (lo, hi) in enumerate(alpha):
        if lo > 0:
            A.append(ge[i][lo])
        if hi < 21:
            A.append(-ge[i][hi + 1])
    return A


def windows_of(dirs, radius, setfile):
    E = json.load(open(os.path.join(DATA, setfile)))['exclusions']
    return sorted(tuple(map(tuple, e['alpha'])) for e in E
                  if tuple(e['dirs']) == tuple(dirs) and e.get('radius', 3) == radius)


def tag_of(dirs):
    return 'd' + ''.join(map(str, dirs)) + '_r3_sym'


def code_of(al):
    z = 0
    for lo, hi in reversed(al):
        d = 6 if (lo, hi) == (6, 21) else lo
        assert (lo, hi) == (6, 21) or (lo == hi and 1 <= lo <= 5), al
        z = z * 8 + d
    return z


def ftag(id_):  # FastRupCmd.tag
    return (id_ * 11400714819323198485 + 7146381651874099225) % 2 ** 64


def L(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def lit(l):
    return f'pos {l}' if l > 0 else f'neg {-l}'


def balanced(names):
    if len(names) == 1:
        return names[0]
    mid = len(names) // 2
    return f'({balanced(names[:mid])} ++ {balanced(names[mid:])})'


def atomic_write(path, s):
    if os.path.exists(path) and open(path).read() == s:
        return          # unchanged: keep the mtime (objects stay up to date)
    tmp = path + '.tmp'
    with open(tmp, 'w') as f:
        f.write(s)
    os.replace(tmp, path)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('work'); ap.add_argument('out'); ap.add_argument('dirs')
    ap.add_argument('--setfile', default='minimal_L7_k6_K5_r3_fix.json')
    ap.add_argument('--block-hints', type=int, default=25000)
    ap.add_argument('--module-hints', type=int, default=400000)
    ap.add_argument('--chunk', type=int, default=32, choices=[32])   # one CRup segment
    ap.add_argument('--g1-chunks', type=int, default=24, help='input chunks per G1 check module')
    ap.add_argument('--tgt-per-module', type=int, default=200)
    ap.add_argument('--win-per-module', type=int, default=60)
    a = ap.parse_args()
    dirs = [int(x) for x in a.dirs.split(',')]
    tag = tag_of(dirs)
    P = 'Q' + ''.join(map(str, dirs))
    work, out = a.work, a.out
    cuts = [tuple(c) for c in json.load(open(os.path.join(work, f'cuts_d{"".join(map(str, dirs))}_r3.json')))]
    enc, ge, roots, nodes, VT, VL, linfo = shape_cnf(dirs, 3, cuts)
    ws = windows_of(dirs, 3, a.setfile)
    clauses = enc.clauses
    ncl = len(clauses)
    stats = dict(tag=tag, dirs=dirs, windows=len(ws), vars=enc.nv, clauses=ncl, cuts=len(cuts), VT=VT, VL=VL)
    # ---------------- the session
    icnf = os.path.join(work, tag + '.icnf')
    s = 'p inccnf\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)
    cubes = [cube(ge, al) for al in ws]
    s += ''.join('a ' + ' '.join(map(str, A)) + ' 0\n' for A in cubes)
    atomic_write(icnf, s)
    stats['icnf_sha256'] = hashlib.sha256(s.encode()).hexdigest()
    trimmed = os.path.join(work, tag + '.trim')
    if not os.path.exists(MTRIM):
        subprocess.run(['gcc', '-O2', '-o', MTRIM, os.path.join(HERE, 'mtrim.c')], check=True)
    if not os.path.exists(trimmed):
        prf = os.path.join(work, tag + '.lidrup')
        t = time.time()
        r = subprocess.run(['nice', '-n', '10', CAD, '-q', '--lidrup', '--no-binary', icnf, prf],
                           capture_output=True, text=True)
        assert 's UNSATISFIABLE' in r.stdout, r.stdout[-2000:]
        stats['solve_s'] = round(time.time() - t, 1)
        rev = trimmed + '.rev'
        subprocess.run(f'tac {prf} | {MTRIM} lidrup {ncl} {rev} > /dev/null', shell=True, check=True)
        subprocess.run(f'tac {rev} > {trimmed}.tmp && mv {trimmed}.tmp {trimmed}', shell=True, check=True)
        os.remove(rev); os.remove(prf)
    # ---------------- parse the trimmed proof
    index = {}
    for i, c in enumerate(clauses, 1):
        index.setdefault(frozenset(c), i)
    idmap = {}          # LIDRUP id -> our id (input index or step id)
    steps = []          # (sid, clause, hints, is_target)
    targets = []        # (window index, sid, clause)
    tclause = {}        # frozenset(clause) -> sid of a target
    nxt = ncl
    for line in open(trimmed):
        t = line.split()
        if t[0] == 'i':
            cl = frozenset(map(int, t[2:-1]))
            if cl in index:
                idmap[int(t[1])] = index[cl]
            else:
                idmap[int(t[1])] = tclause[cl]
        elif t[0] == 'l':
            z = t.index('0', 2)
            cl = list(map(int, t[2:z])); hs = [idmap[int(h)] for h in t[z + 1:-1]]
            nxt += 1; idmap[int(t[1])] = nxt
            steps.append((nxt, cl, hs, False))
        elif t[0] == 'u':
            z = t.index('0', 1)
            core = list(map(int, t[1:z])); hs = [idmap[int(h)] for h in t[z + 1:-1]]
            w = len(targets)
            assert set(core) <= set(cubes[w]), ('core not in cube', w)
            cl = [-x for x in core]
            nxt += 1
            steps.append((nxt, cl, hs, True))
            targets.append((w, nxt, cl))
            tclause.setdefault(frozenset(cl), nxt)
    assert len(targets) == len(ws), (len(targets), len(ws))
    assert all(h > 0 for _, _, hs, _ in steps for h in hs)
    H = sum(len(hs) for _, _, hs, _ in steps)
    stats.update(steps=len(steps), hints=H, targets=len(targets))
    # ---------------- FastRup modules (gen_fast.py layout, plus target exports)
    nv = enc.nv
    Wo = nv + 1
    used = sorted({h for _, _, hs, _ in steps for h in hs if h <= ncl})
    touched = sorted({abs(l) for i in used for l in clauses[i - 1]} | {abs(l) for _, c, _, _ in steps for l in c})
    new = {v: i + 1 for i, v in enumerate(touched)}
    W = len(touched) + 1
    Bb = max(1, nv.bit_length())
    S = 64 + 2 * W                      # CRup slot width
    T = 0
    for v, i in new.items():
        T |= v << (i * Bb)
    posO = lambda l: l if l > 0 else Wo - l
    posR = lambda l: new[l] if l > 0 else W + new[-l]
    hdr = 'set_option maxRecDepth 100000\nset_option Elab.async false\n'
    files = []
    chunks = [used[i:i + a.chunk] for i in range(0, len(used), a.chunk)]
    chunk_of = {i: k for k, ch in enumerate(chunks) for i in ch}
    usha = hashlib.sha256(''.join(' '.join(map(str, clauses[i - 1])) + ' 0\n' for i in used).encode()).hexdigest()
    s = f'import CRupCmd\n{hdr}namespace {P}\nopen WinCNF\n'
    s += (f'/-! The {len(used)} clauses (of {ncl}) of the shape CNF of `{tag}` (dirs {dirs}, radius 3,\n'
          f'shape CNF + cubes sha256 {stats["icnf_sha256"]}) used by the trimmed shared proof, in original order\n'
          f'(sha256 of their DIMACS lines: {usha}).  `fr_cnf` records are `index positions… 0`, stride {Wo}. -/\n')
    s += f'fr_cnf {Wo} {a.chunk}\n'
    s += '\n'.join(f'{i} ' + ' '.join(str(posO(l)) for l in clauses[i - 1]) + ' 0' for i in used) + '\n'
    s += f'/-- The used input clauses. -/\nnoncomputable def F : CNF := {balanced([f"G{k}" for k in range(len(chunks))])}\n'
    s += 'def Inp (τ : Nat → Bool) : Prop := ∀ c ∈ F, clauseSat τ c\n'
    s += f'def RT : Nat := {hex(T)}\n'
    for k, ch in enumerate(chunks):
        s += f'fr_chunk {k} {W} {Bb} ' + ' '.join(str(new[abs(l)]) for i in ch for l in clauses[i - 1]) + '\n'
        s += f'cr_chunk {k} {S}\n'
    s += f'end {P}\n'
    files.append((f'{P}Inputs', s))
    blocks, cur, ch = [], [], 0
    for st in steps:
        cur.append(st); ch += len(st[2])
        if ch >= a.block_hints:
            blocks.append(cur); cur, ch = [], 0
    if cur:
        blocks.append(cur)
    home = {sid: b for b, blk in enumerate(blocks, 1) for sid, _, _, _ in blk}
    exports = {b: set() for b in range(1, len(blocks) + 1)}
    for b, blk in enumerate(blocks, 1):
        for _, _, hs, _ in blk:
            for h in hs:
                if h > ncl and home[h] != b:
                    exports[home[h]].add(h)
    for _, sid, _ in targets:
        exports[home[sid]].add(sid)
    exp_order = {b: sorted(e) for b, e in exports.items()}
    mods, mcur, mh = [], [], 0
    for b, blk in enumerate(blocks, 1):
        mcur.append(b); mh += sum(len(x[2]) for x in blk)
        if mh >= a.module_hints:
            mods.append(mcur); mcur, mh = [], 0
    if mcur:
        mods.append(mcur)
    prev = f'{P}Inputs'
    for m, bl in enumerate(mods):
        s = f'import {prev}\n{hdr}namespace {P}\n'
        for b in bl:
            blk = blocks[b - 1]
            ext = {h for _, _, hs, _ in blk for h in hs if h <= ncl or home[h] != b}
            rch = sorted({chunk_of[h] for h in ext if h <= ncl})
            rbl = sorted({home[h] for h in ext if h > ncl})
            slot, n = {}, 0
            for k in rch:                       # a chunk is one segment of 32 slots
                for j, i in enumerate(chunks[k]):
                    slot[i] = n + j
                n += 32
            for rb in rbl:                      # a block's exports, padded to whole segments
                for e in exp_order[rb]:
                    slot[e] = n; n += 1
                n += -n % 32
            for sid, _, _, _ in blk:
                slot[sid] = n; n += 1
            provs = [2 * k + 1 for k in rch] + [2 * rb for rb in rbl]
            sel = [slot[e] + 1 for e in exp_order[b]]
            sel += [0] * (-len(sel) % 32)
            data = [len(provs)] + provs + [len(sel)] + sel
            s += f'cr_block B{b} {W} {Bb} {S} ' + ' '.join(map(str, data)) + '\n'
            for sid, c, hs, _ in blk:
                s += f'{sid} ' + ' '.join(str(posR(l)) for l in c) + (' 0 ' if c else '0 ') + ' '.join(str(slot[h] + 1) for h in hs) + ' 0\n'
        s += f'end {P}\n'
        files.append((f'{P}S{m:02d}', s))
        prev = f'{P}S{m:02d}'
    # targets: fr_tgt modules (each imports the last step module)
    last_step = prev
    tmods = []
    for j in range(0, len(targets), a.tgt_per_module):
        s = f'import {last_step}\n{hdr}namespace {P}\n'
        for w, sid, cl in targets[j:j + a.tgt_per_module]:
            b = home[sid]
            k = exp_order[b].index(sid)
            s += (f'cr_tgt t{w} B{b} {k} {W} {Bb} {Wo} ' + ' '.join(str(posO(l)) for l in cl) + ' 0 '
                  + ' '.join(str(new[abs(l)]) for l in cl) + f' 0 {ftag(sid)}\n')
        s += f'end {P}\n'
        name = f'{P}Tgt{len(tmods)}'
        files.append((name, s)); tmods.append(name)
    # ---------------- G1 data
    nb = len(enc.ball)
    ends = [v for v in enc.ball if all(v ^ 1 << k in enc.B for k in range(9))]
    ne = len(ends)
    assert len(enc.blocks) == 1 and enc.blocks[0][3] == 'endpoint_budget'
    assert enc.blocks[0][2] == list(range(nb + 1, nb + ne + 1))
    window = window_from_dirs(dirs)
    s = f'import Sh235Win\nimport {P}Inputs\n'
    s += (f'/-! G1 data of the shape CNF `{tag}` (dirs {dirs}): tables, lex generators, totalizer nodes.\n'
          'Generated by u235/gen235.py; untrusted, every fact is decided by the kernel. -/\n')
    s += f'namespace {P}\nopen WinCNF W223G1 WinG1 D239 S235\nset_option maxRecDepth 100000\n'
    s += f'noncomputable def ballL : List Nat := {L(enc.ball)}\n'
    s += f'noncomputable def endsL : List Nat := {L(ends)}\n'
    b0, k0, l0, _ = enc.blocks[0]
    s += f'noncomputable def B0 : Block := ⟨{b0}, {k0}, {len(l0)}, [' + ', '.join(lit(x) for x in l0) + ']⟩\n'
    s += f'noncomputable def T : Tables := ⟨{nb}, {ne}, ballL, endsL, {L(window)}, [B0]⟩\n'
    for g, (ga, gb, base, npairs) in enumerate(linfo):
        pr = [(v, symsolve.swapN(ga, gb, v)) for v in enc.ball if symsolve.swapN(ga, gb, v) != v]
        assert len(pr) == npairs
        s += f'noncomputable def X{g} : LexT := ⟨[' + ', '.join(f'({v}, {w})' for v, w in pr) + f'], {base}⟩\n'
    s += 'noncomputable def X : List LexT := [' + ', '.join(f'X{g}' for g in range(len(linfo))) + ']\n'
    s += 'noncomputable def Tot : List TotNode := [\n  ' + ',\n  '.join(
        f'⟨{base}, [' + ', '.join(lit(x) for x in ls) + ']⟩' for base, ls in nodes) + ']\n'
    s += f'noncomputable def D : Sh := ⟨T, X, Tot, {VT}, {VL}⟩\n'
    s += f'def c : List Nat := {L(dirs)}\n'
    s += f'def roots : List Nat := {L(roots)}\n'
    s += 'theorem hD : shOK D = true := by decide +kernel\n'
    s += 'theorem hok : blocksOK D.T = true := by decide +kernel\n'
    s += 'theorem hT : tabOK D.T [] = true := by decide +kernel\n'
    s += 'theorem hwin : D.T.window = winL c := by decide +kernel\n'
    s += 'theorem h9 : c.all (· < 9) = true := by decide +kernel\n'
    s += ('theorem hlex : D.X.map LexT.pairs = (adjP (freeC (c.map coordOf))).map\n'
          '    (fun g => movedPairs D.T.ball g.1.val g.2.val) := by decide +kernel\n')
    s += 'theorem hcen : (cenOf c roots).all (cenOK D) = true := by decide +kernel\n'
    s += ('theorem hco : ∀ t ∈ cenOf c roots, CornerOK t.2.1 (coordOf t.2.2.1) (coordOf t.2.2.2)\n'
          '    (cornerVerts t.2.1 t.2.2.1 t.2.2.2) := by unfold CornerOK; decide +kernel\n')
    s += f'end {P}\n'
    files.append((f'{P}G1', s))
    cm = [list(range(i, min(i + a.g1_chunks, len(chunks)))) for i in range(0, len(chunks), a.g1_chunks)]
    for j, ks in enumerate(cm):
        s = f'import {P}G1\nnamespace {P}\nopen WinCNF S235\nset_option maxRecDepth 100000\n'
        for k in ks:
            s += f'theorem chk{k} : G{k}.all (check3 D) = true := by decide +kernel\n'
        s += f'end {P}\n'
        files.append((f'{P}G1C{j}', s))
    # ---------------- the shape theorem: checkF, window theorems in groups, the cons chain
    s = ''.join(f'import {P}G1C{j}\n' for j in range(len(cm))) + f'import {P}Inputs\n'
    s += f'namespace {P}\nopen WinCNF S235\nset_option maxRecDepth 100000\n'
    s += ('theorem checkF : F.all (check3 D) = true := by\n  simp only [F, List.all_append, '
          + ', '.join(f'chk{k}' for k in range(len(chunks))) + ', Bool.and_self]\n')
    s += f'end {P}\n'
    files.append((f'{P}Chk', s))
    k = len(dirs) - 1
    wmods = []
    for j in range(0, len(ws), a.win_per_module):
        s = f'import {P}Chk\n' + ''.join(f'import {t}\n' for t in tmods)
        s += f'namespace {P}\nopen WinCNF S235\nset_option maxRecDepth 100000\n'
        for w in range(j, min(j + a.win_per_module, len(ws))):
            s += (f'theorem w{w} : WinRef c (decR {k} {code_of(ws[w])}) :=\n'
                  f'  winRef_of hD hok hT checkF hwin h9 hlex hcen hco (by decide) t{w} (by decide +kernel)\n')
        s += f'end {P}\n'
        name = f'{P}W{len(wmods)}'
        files.append((name, s)); wmods.append(name)
    s = ''.join(f'import {m}\n' for m in wmods)
    s += f'/-! Every window of shape `{dirs}` of the 235 premise set is refuted ({len(ws)} windows). -/\n'
    s += f'namespace {P}\nopen WinCNF S235\nset_option maxRecDepth 100000\n'
    s += f'theorem refuted : ShapeRefuted c ([' + ', '.join(str(code_of(al)) for al in ws) + f'].map (decR {k})) :=\n  '
    term = 'shapeRefuted_nil c'
    for w in reversed(range(len(ws))):
        term = f'shapeRefuted_cons w{w} ({term})'
    s += term + '\n'
    s += f'end {P}\n'
    files.append((f'{P}Ref', s))
    os.makedirs(out, exist_ok=True)
    shas = {}
    for name, src in files:
        atomic_write(os.path.join(out, name + '.lean'), src)
        shas[name] = hashlib.sha256(src.encode()).hexdigest()
    stats.update(used_inputs=len(used), W=W, blocks=len(blocks), step_modules=len(mods),
                 modules=[n for n, _ in files], sources_sha256=shas, used_sha256=usha)
    atomic_write(os.path.join(work, tag + '.gen.json'), json.dumps(stats, indent=1))
    print(json.dumps({k: v for k, v in stats.items() if k not in ('sources_sha256', 'modules')}))
    print(' '.join(n for n, _ in files))


if __name__ == '__main__':
    main()
