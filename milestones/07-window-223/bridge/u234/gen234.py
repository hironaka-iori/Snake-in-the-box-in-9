"""Share bridge for the 234 bound: one share CNF per six-centre shape (the committed certificate CNF
of milestones/10-window-aggregate/data/share/final_a_X20.jsonl), a CaDiCaL LRAT proof checked by CRup
(G2), and the kernel-checked G1 data and checks (`SH234.check4`, `nodesOK`, `termsOK`).

usage: python3 -I gen234.py WORK OUTDIR DIRS [--block-hints N] [--module-hints M] [--g1-chunks K]

Writes WORK/<tag>.cnf (sha256 must equal the recorded cnf_sha256), runs CaDiCaL 2.1.3 --lrat
(deterministic), trims the proof backwards from the empty clause, and writes the Lean modules of
prefix V<dirs> to OUTDIR, plus WORK/<tag>.gen.json (statistics, sha256 of the proof and of every module).

Everything emitted is untrusted: the kernel re-checks every RUP step (CRup), every used input clause
against the G1 checker and the term and node tables against the share definition (`SH234.shareRef_of`).
"""
import argparse, hashlib, json, os, subprocess, sys, time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.environ.get('REPO', os.path.abspath(os.path.join(HERE, '..', '..', '..', '..')))
sys.path.insert(0, os.path.join(REPO, 'milestones', '10-window-aggregate', 'scripts'))
from share_enc import ShareEncoding, window_from_dirs  # noqa: E402

DATA = os.path.join(REPO, 'milestones', '10-window-aggregate', 'data', 'share')
CAD = os.environ.get('CADICAL', '/root/.elan/toolchains/leanprover--lean4---v4.19.0/bin/cadical')
X = 20


class Rec(ShareEncoding):
    """ShareEncoding with the same clauses, recording the counter blocks and the totalizer nodes."""

    def atmost(self, lits, k, kind):
        if not hasattr(self, 'blocks'):
            self.blocks = []
        base = self.nv + 1
        super().atmost(lits, k, kind)
        if 0 < k < len(lits):
            assert self.nv == base - 1 + len(lits) * k
            self.blocks.append((base, k, list(lits), kind))

    # a counter operand: dict(vec=unary literals, lo, hi, bits=term bits or None)
    def _mergeR(self, A, Bv, cap):
        base = self.nv + 1
        O = self._merge(A['vec'], Bv['vec'], cap)
        assert O == list(range(base, base + len(O)))
        assert A['hi'] == Bv['lo']
        n = dict(vec=O, lo=A['lo'], hi=Bv['hi'], bits=None, base=base,
                 mid=A['hi'], lb=A['bits'] or [], rb=Bv['bits'] or [])
        self.nodes.append(n)
        return n

    def cnt_stot(self, B):
        cap = B + 1
        self.nodes = []
        ncent = len(self.window) - 2
        acc = None
        for ci in range(ncent):
            idx = [t for t, (c, _) in enumerate(self.terms) if c == ci]
            assert idx == list(range(idx[0], idx[-1] + 1))
            leaves = [dict(vec=self.terms[t][1][:cap], lo=t, hi=t + 1, bits=self.terms[t][1]) for t in idx]
            while len(leaves) > 1:
                nxt = [self._mergeR(leaves[i], leaves[i + 1], cap) for i in range(0, len(leaves) - 1, 2)]
                if len(leaves) % 2:
                    nxt.append(leaves[-1])
                leaves = nxt
            u = leaves[0]
            acc = u if acc is None else self._mergeR(acc, u, cap)
            assert acc['bits'] is None
            if len(acc['vec']) >= cap:
                self.add([-acc['vec'][cap - 1]], 'stot_bound')
                acc = dict(acc, vec=acc['vec'][:cap - 1])


def share_keys(window):
    """(centre index, k, a, b, Q, P) in ShareEncoding's order (share_enc.share_terms with keys)."""
    for i, c in enumerate(window[1:-1], 1):
        used = {(c ^ window[i - 1]).bit_length() - 1, (c ^ window[i + 1]).bit_length() - 1}
        for k in [d for d in range(9) if d not in used]:
            y = c ^ 1 << k
            for a, b in combinations([d for d in range(9) if d != k], 2):
                Q = tuple(sorted({y, y ^ 1 << a, y ^ 1 << b, y ^ 1 << a ^ 1 << b}))
                yield i - 1, k, a, b, Q, (c ^ 1 << a, c ^ 1 << b, c ^ 1 << a ^ 1 << b)


def L(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def lit(l):
    return f'pos {l}' if l > 0 else f'neg {-l}'


def ginfo(e, pv, t):
    assert e < 65536 and t < 4 and len(pv) < 4
    return 2 | e << 2 | t << 18 | len(pv) << 20 | sum(w << (22 + 9 * i) for i, w in enumerate(pv))


def bt(items):
    """Lean term of the index tree `SH234.BT` (root 0, odd -> left, even -> right)."""
    if not items:
        return 'BT.nil'
    return f'(BT.node {bt(items[1::2])} {items[0]} {bt(items[2::2])})'


def pack(xs, w):
    """A table of fixed-width fields as a `BT` of chunks of 64 fields (`SH234.tget`)."""
    out = []
    for c in range(0, max(len(xs), 1), 64):
        z = 0
        for i, x in enumerate(xs[c:c + 64]):
            assert 0 <= x < 2 ** w
            z |= x << (w * i)
        out.append(hex(z))
    return bt(out)


def tpack(ci, k, a, b, e, bits):
    assert ci < 8 and k < 16 and a < 16 and b < 16 and e < 65536 and len(bits) < 8
    assert all(0 < v < 65536 for v in bits)
    return ci | k << 3 | a << 7 | b << 11 | e << 15 | len(bits) << 31 | sum(v << (34 + 16 * i) for i, v in enumerate(bits))


def npack(nd, terms):
    lo, mid, hi = nd['lo'], nd['mid'], nd['hi']
    assert hi < 2048
    fl, fr = int(bool(nd['lb'])), int(bool(nd['rb']))
    assert not fl or nd['lb'] == terms[lo][5]
    assert not fr or nd['rb'] == terms[mid][5]
    return lo | mid << 11 | hi << 22 | fl << 33 | fr << 34


def balanced(names):
    if len(names) == 1:
        return names[0]
    mid = len(names) // 2
    return f'({balanced(names[:mid])} ++ {balanced(names[mid:])})'


def atomic_write(path, s):
    if os.path.exists(path) and open(path).read() == s:
        return
    tmp = path + '.tmp'
    with open(tmp, 'w') as f:
        f.write(s)
    os.replace(tmp, path)


def lrat_trim(ncl, inp, out):
    steps, order, last = {}, [], None
    for line in open(inp):
        t = line.split()
        if not t or t[1] == 'd':
            continue
        xs = list(map(int, t)); z = xs.index(0, 1)
        steps[xs[0]] = (xs[1:z], xs[z + 1:-1]); order.append(xs[0])
        if z == 1:
            last = xs[0]; break
    need, stack = {last}, [last]
    while stack:
        s = stack.pop()
        for h in steps[s][1]:
            assert h > 0, 'RAT hint'
            if h > ncl and h not in need:
                need.add(h); stack.append(h)
    with open(out, 'w') as f:
        for sid in order:
            if sid in need:
                c, hs = steps[sid]
                f.write(f"{sid} {' '.join(map(str, c))} 0 {' '.join(map(str, hs))} 0\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('work'); ap.add_argument('out'); ap.add_argument('dirs')
    ap.add_argument('--block-hints', type=int, default=25000)
    ap.add_argument('--module-hints', type=int, default=1000000)
    ap.add_argument('--g1-chunks', type=int, default=160, help='input chunks per G1 check module')
    a = ap.parse_args()
    dirs = [int(x) for x in a.dirs.split(',')]
    key = ','.join(map(str, dirs))
    tag = 'd' + ''.join(map(str, dirs)) + '_share20'
    P = 'V' + ''.join(map(str, dirs))
    rec = [r for r in map(json.loads, open(os.path.join(DATA, 'final_a_X20.jsonl'))) if r['dirs'] == dirs]
    assert len(rec) == 1 and rec[0]['X'] == X and rec[0]['status'] == 'UNSAT'
    rec = rec[0]
    cuts = json.load(open(os.path.join(DATA, 'final_a_X20.jsonl.cuts.json')))[key]
    window = window_from_dirs(dirs)
    k6 = len(dirs) - 1
    enc = Rec(window, [(0, 21)] * k6, 3, X, counter='stot', exact=True)
    for c in cuts:
        enc.add_cycle_cut(c)
    clauses = enc.clauses
    ncl = len(clauses)
    cnf = os.path.join(a.work, tag + '.cnf')
    s = f'p cnf {enc.nv} {ncl}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)
    assert hashlib.sha256(s.encode()).hexdigest() == rec['cnf_sha256'], 'CNF differs from the certificate'
    atomic_write(cnf, s)
    stats = dict(tag=tag, dirs=dirs, vars=enc.nv, clauses=ncl, cuts=len(cuts), cnf_sha256=rec['cnf_sha256'])
    # ---------------- G1 tables
    W = set(window)
    VS = min(enc.esq.values())
    assert all(abs(l) < VS for c in clauses[:enc.n_base] for l in c)
    assert all(abs(l) < VS for c, kd in zip(clauses, enc.kinds) if kd == 'cycle_cut' for l in c)
    VE = enc.nv + 1
    info = {}
    for Q, e in enc.esq.items():
        assert len(Q) == 4
        info[e] = 1 | sum(w << (2 + 9 * i) for i, w in enumerate(Q))
    terms = []
    it = iter(enc.terms)
    for ci, k, aa, bb, Q, Pc in share_keys(window):
        if any(w in W for w in Q):
            continue
        ci2, bits = next(it)
        assert ci2 == ci and bits[0] == bits[1] == enc.esq[Q]
        E = enc.esq[Q]
        nfix = sum(w in W for w in Pc)
        pv = [w for w in Pc if w not in W]
        if nfix <= 1:
            g1 = bits[2]
            assert g1 not in info
            info[g1] = ginfo(E, pv, 1 - nfix)
        if nfix == 0:
            g3 = bits[3]
            assert bits[3:] == [g3] * 3 and g3 not in info
            info[g3] = ginfo(E, pv, 0)
        assert len(bits) == {0: 6, 1: 3}.get(nfix, 2)
        terms.append((ci, k, aa, bb, E, bits))
    assert next(it, None) is None
    NT = len(terms)
    for n, nd in enumerate(enc.nodes):
        for j in range(1, len(nd['vec']) + 1):
            v = nd['base'] + j - 1
            assert v not in info
            assert n < 65536 and j < 256
            info[v] = 3 | n << 2 | j << 18
    assert sorted(info) == list(range(VS, VE)), 'share variables not contiguous'
    assert len(enc.blocks) == 1 and enc.blocks[0][3] == 'endpoint_budget'
    nb = len(enc.ball)
    ends = [v for v in enc.ball if all(v ^ 1 << k in enc.B for k in range(9))]
    assert enc.blocks[0][2] == list(range(nb + 1, nb + len(ends) + 1))
    stats.update(VS=VS, VE=VE, terms=NT, nodes=len(enc.nodes))
    # ---------------- proof
    lrat = os.path.join(a.work, tag + '.lrat')
    trim = os.path.join(a.work, tag + '.trim')
    if not os.path.exists(trim):
        t = time.time()
        r = subprocess.run(['nice', '-n', '19', CAD, '-q', '--lrat', '--no-binary', cnf, lrat],
                           capture_output=True, text=True)
        assert 's UNSATISFIABLE' in r.stdout, r.stdout[-2000:]
        stats['solve_s'] = round(time.time() - t, 1)
        lrat_trim(ncl, lrat, trim + '.tmp')
        os.replace(trim + '.tmp', trim)
        os.remove(lrat)
    stats['trim_sha256'] = hashlib.sha256(open(trim, 'rb').read()).hexdigest()
    steps = []
    for line in open(trim):
        xs = list(map(int, line.split()))
        z = xs.index(0, 1)
        steps.append((xs[0], xs[1:z], xs[z + 1:-1]))
    assert steps[-1][1] == []
    # ---------------- CRup modules (gen_crup.py layout)
    nv = enc.nv
    Wo = nv + 1
    used = sorted({h for _, _, hs in steps for h in hs if h <= ncl})
    touched = sorted({abs(l) for i in used for l in clauses[i - 1]} | {abs(l) for _, c, _ in steps for l in c})
    new = {v: i + 1 for i, v in enumerate(touched)}
    Wr = len(touched) + 1
    Bb = max(1, nv.bit_length())
    S = 64 + 2 * Wr
    T = 0
    for v, i in new.items():
        T |= v << (i * Bb)
    posO = lambda l: l if l > 0 else Wo - l
    posR = lambda l: new[l] if l > 0 else Wr + new[-l]
    hdr = 'set_option maxRecDepth 100000\nset_option Elab.async false\n'
    files = []
    CH = 32
    chunks = [used[i:i + CH] for i in range(0, len(used), CH)]
    chunk_of = {i: k for k, ch in enumerate(chunks) for i in ch}
    usha = hashlib.sha256(''.join(' '.join(map(str, clauses[i - 1])) + ' 0\n' for i in used).encode()).hexdigest()
    s = f'import CRupCmd\n{hdr}namespace {P}\nopen WinCNF\n'
    s += (f'/-! The {len(used)} clauses (of {ncl}) of the share CNF of `{tag}` (dirs {dirs}, bound {X},\n'
          f'sha256 {rec["cnf_sha256"]}) used by the trimmed LRAT proof, in original order\n'
          f'(sha256 of their DIMACS lines: {usha}).  `fr_cnf` records are `index positions… 0`, stride {Wo}. -/\n')
    s += f'fr_cnf {Wo} {CH}\n'
    s += '\n'.join(f'{i} ' + ' '.join(str(posO(l)) for l in clauses[i - 1]) + ' 0' for i in used) + '\n'
    s += f'/-- The used input clauses. -/\nnoncomputable def F : CNF := {balanced([f"G{k}" for k in range(len(chunks))])}\n'
    s += 'def Inp (τ : Nat → Bool) : Prop := ∀ c ∈ F, clauseSat τ c\n'
    s += f'def RT : Nat := {hex(T)}\n'
    for k, ch in enumerate(chunks):
        s += f'fr_chunk {k} {Wr} {Bb} ' + ' '.join(str(new[abs(l)]) for i in ch for l in clauses[i - 1]) + '\n'
        s += f'cr_chunk {k} {S}\n'
    s += f'end {P}\n'
    files.append((f'{P}Inputs', s))
    blocks, cur, chh = [], [], 0
    for st in steps:
        cur.append(st); chh += len(st[2])
        if chh >= a.block_hints:
            blocks.append(cur); cur, chh = [], 0
    if cur:
        blocks.append(cur)
    home = {sid: b for b, blk in enumerate(blocks, 1) for sid, _, _ in blk}
    exports = {b: set() for b in range(1, len(blocks) + 1)}
    for b, blk in enumerate(blocks, 1):
        for _, _, hs in blk:
            for h in hs:
                if h > ncl and home[h] != b:
                    exports[home[h]].add(h)
    exports[len(blocks)].add(steps[-1][0])
    exp_order = {b: sorted(e) for b, e in exports.items()}
    mods, mcur, mh = [], [], 0
    for b, blk in enumerate(blocks, 1):
        mcur.append(b); mh += sum(len(x[2]) for x in blk)
        if mh >= a.module_hints:
            mods.append(mcur); mcur, mh = [], 0
    if mcur:
        mods.append(mcur)
    prev = f'{P}Inputs'
    H = 0
    for m, bl in enumerate(mods):
        s = f'import {prev}\n{hdr}namespace {P}\n'
        for b in bl:
            blk = blocks[b - 1]
            ext = {h for _, _, hs in blk for h in hs if h <= ncl or home[h] != b}
            rch = sorted({chunk_of[h] for h in ext if h <= ncl})
            rbl = sorted({home[h] for h in ext if h > ncl})
            slot, n = {}, 0
            for k in rch:
                for j, i in enumerate(chunks[k]):
                    slot[i] = n + j
                n += 32
            for rb in rbl:
                for e in exp_order[rb]:
                    slot[e] = n; n += 1
                n += -n % 32
            for sid, _, _ in blk:
                slot[sid] = n; n += 1
            provs = [2 * k + 1 for k in rch] + [2 * rb for rb in rbl]
            sel = [slot[e] + 1 for e in exp_order[b]]
            sel += [0] * (-len(sel) % 32)
            data = [len(provs)] + provs + [len(sel)] + sel
            s += f'cr_block B{b} {Wr} {Bb} {S} ' + ' '.join(map(str, data)) + '\n'
            for sid, c, hs in blk:
                H += len(hs)
                s += f'{sid} ' + ' '.join(str(posR(l)) for l in c) + (' 0 ' if c else '0 ') + ' '.join(str(slot[h] + 1) for h in hs) + ' 0\n'
        s += f'end {P}\n'
        files.append((f'{P}S{m:02d}', s))
        prev = f'{P}S{m:02d}'
    s = f'import {prev}\n{hdr}open WinCNF\n'
    s += (f'/-! `{P}.F` is unsatisfiable: {len(steps)} RUP steps, {H} hints, {len(blocks)} kernel-checked blocks. -/\n'
          f'namespace {P}\ncr_main unsatF B{len(blocks)} {exp_order[len(blocks)].index(steps[-1][0])}\nend {P}\n')
    files.append((f'{P}Main', s))
    stats.update(used_inputs=len(used), steps=len(steps), hints=H, blocks=len(blocks), step_modules=len(mods))
    # ---------------- G1 data module
    s = f'import ShareNorm\nimport {P}Inputs\nset_option Elab.async false\n'
    s += (f'/-! G1 data of the share CNF `{tag}` (dirs {dirs}, bound {X}): ball tables, share variables\n'
          '(`Info`), totalizer nodes, share terms.  Generated by u234/gen234.py; untrusted, every fact is\n'
          'decided by the kernel. -/\n')
    s += f'namespace {P}\nopen WinCNF W223G1 WinG1 S235 SH234\nset_option maxRecDepth 100000\n'
    s += f'noncomputable def ballL : List Nat := {L(enc.ball)}\n'
    s += f'noncomputable def endsL : List Nat := {L(ends)}\n'
    b0, k0, l0, _ = enc.blocks[0]
    s += f'noncomputable def B0 : Block := ⟨{b0}, {k0}, {len(l0)}, [' + ', '.join(lit(x) for x in l0) + ']⟩\n'
    s += f'noncomputable def T : Tables := ⟨{nb}, {len(ends)}, ballL, endsL, {L(window)}, [B0]⟩\n'
    s += f'noncomputable def I : BT := {pack([info[v] for v in range(VS, VE)], 64)}\n'
    s += f'noncomputable def ND : BT := {pack([npack(nd, terms) for nd in enc.nodes], 64)}\n'
    s += f'noncomputable def TD : BT := {pack([tpack(*t) for t in terms], 192)}\n'
    s += f'noncomputable def D : SD := ⟨T, {VS}, {VE}, I, {len(enc.nodes)}, ND, {NT}, TD, {X}⟩\n'
    s += f'def c : List Nat := {L(dirs)}\n'
    s += 'theorem hD : sdOK D = true := by decide +kernel\n'
    s += 'theorem hok : blocksOK D.T = true := by decide +kernel\n'
    s += 'theorem hT : tabOK D.T [] = true := by decide +kernel\n'
    s += 'theorem hwin : D.T.window = winL c := by decide +kernel\n'
    def chunked(name, pred, n, nexpr, step, ty, wrap):
        out, los = '', list(range(0, n, step))
        for j, lo in enumerate(los):
            out += f'theorem {name}{j} : allFrom ({pred}) {lo} {min(step, n - lo)} = true := by decide +kernel\n'
        term = f'chunk_end (p := {pred}) (n := {nexpr}) (lo := {n}) (by decide +kernel)'
        for j in reversed(range(len(los))):
            term = f'chunk_step {name}{j} ({term})'
        return out + f'theorem {name} : {ty} := {wrap(term)}\n'
    NN = len(enc.nodes)
    s += chunked('hN', 'nodeOK D', NN, 'D.NN', 200, 'NodesOK D', lambda t: f'fun n hn => ({t}) n (Nat.zero_le _) hn')
    s += chunked('hT1', 'termOK D c', NT, 'D.NT', 100, '∀ t < D.NT, termOK D c t = true',
                 lambda t: f'fun t ht => ({t}) t (Nat.zero_le _) ht')
    s += chunked('hT2', 'codeLt D', NT - 1, str(NT - 1), 400, '∀ t, t + 1 < D.NT → codeLt D t = true',
                 lambda t: f'fun t ht => ({t}) t (Nat.zero_le _) (by have : D.NT = {NT} := rfl; omega)')
    s += 'theorem hterms : TermsOK D c := ⟨hT1, hT2⟩\n'
    s += f'end {P}\n'
    files.append((f'{P}G1', s))
    cm = [list(range(i, min(i + a.g1_chunks, len(chunks)))) for i in range(0, len(chunks), a.g1_chunks)]
    for j, ks in enumerate(cm):
        s = f'import {P}G1\nset_option Elab.async false\nnamespace {P}\nopen WinCNF SH234\nset_option maxRecDepth 100000\n'
        for k in ks:
            s += f'theorem chk{k} : G{k}.all (check4 D) = true := by decide +kernel\n'
        s += f'end {P}\n'
        files.append((f'{P}G1C{j}', s))
    s = ''.join(f'import {P}G1C{j}\n' for j in range(len(cm))) + f'import {P}Main\n'
    s += (f'/-! Every snake through the window of shape `{dirs}` has share sum at least {X + 1} over its\n'
          f'{k6} centres (`SH234.ShareRef`). -/\n')
    s += f'namespace {P}\nopen WinCNF SH234\nset_option maxRecDepth 100000\n'
    s += ('theorem checkF : F.all (check4 D) = true := by\n  simp only [F, List.all_append, '
          + ', '.join(f'chk{k}' for k in range(len(chunks))) + ', Bool.and_self]\n')
    s += f'theorem ref : ShareRef c {X + 1} :=\n  shareRef_of unsatF hD hN hok hT checkF hterms hwin (by decide)\n'
    s += f'end {P}\n'
    files.append((f'{P}Ref', s))
    os.makedirs(a.out, exist_ok=True)
    shas = {}
    for name, src in files:
        atomic_write(os.path.join(a.out, name + '.lean'), src)
        shas[name] = hashlib.sha256(src.encode()).hexdigest()
    stats.update(modules=[n for n, _ in files], sources_sha256=shas, used_sha256=usha)
    atomic_write(os.path.join(a.work, tag + '.gen.json'), json.dumps(stats, indent=1))
    print(json.dumps({k: v for k, v in stats.items() if k not in ('sources_sha256', 'modules')}))
    print(' '.join(n for n, _ in files))


if __name__ == '__main__':
    main()
