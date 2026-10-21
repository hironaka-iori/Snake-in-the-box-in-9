"""LRAT -> Lean modules for the FastRup checker (untrusted: the kernel re-checks everything).

usage: gen_fast.py CNF LRAT OUTDIR NAMESPACE [--block-hints N] [--module-hints M] [--chunk C]

Writes OUTDIR/Inputs.lean (used input clauses, renaming table, CPS input chunks `I{k}`),
OUTDIR/Snn.lean (`fr_block` commands, CPS block theorems `B{b}`) and OUTDIR/Main.lean
(`theorem <ns>_unsat : WinCNF.unsat <ns>.F`), and prints the module list in build order.

Variables touched by the proof are renumbered densely (1..n) inside the checker; the table `RT`
maps them back and every input clause is re-checked against it by the kernel.
"""
import argparse, hashlib, os, sys


def read_cnf(path):
    nv, cls = 0, []
    for line in open(path):
        if line.startswith('p'):
            nv = int(line.split()[2])
        elif line[0] not in 'c\n':
            xs = list(map(int, line.split()))
            assert xs[-1] == 0
            cls.append(xs[:-1])
    return nv, cls


def read_lrat(path, ncl):
    steps = []
    for line in open(path):
        t = line.split()
        if not t or t[1] == 'd':
            continue
        xs = list(map(int, t))
        z = xs.index(0, 1)
        sid, c, hs = xs[0], xs[1:z], xs[z + 1:-1]
        assert sid > ncl and hs and all(h > 0 for h in hs), f'RAT or odd step {sid}'
        steps.append((sid, c, hs))
        if not c:
            break
    assert steps[-1][1] == [], 'proof must end with the empty clause'
    return steps


def balanced(names):
    if len(names) == 1:
        return names[0]
    mid = len(names) // 2
    return f'({balanced(names[:mid])} ++ {balanced(names[mid:])})'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cnf'); ap.add_argument('lrat'); ap.add_argument('outdir'); ap.add_argument('ns')
    ap.add_argument('--block-hints', type=int, default=25000)
    ap.add_argument('--module-hints', type=int, default=250000)
    ap.add_argument('--chunk', type=int, default=32)
    a = ap.parse_args()
    nv, cls = read_cnf(a.cnf)
    ncl = len(cls)
    steps = read_lrat(a.lrat, ncl)
    Wo = nv + 1
    used = sorted({h for _, _, hs in steps for h in hs if h <= ncl})
    # dense renumbering of the touched variables
    touched = sorted({abs(l) for i in used for l in cls[i - 1]} | {abs(l) for _, c, _ in steps for l in c})
    new = {v: i + 1 for i, v in enumerate(touched)}
    W = len(touched) + 1
    Bb = max(1, nv.bit_length())
    T = 0
    for v, i in new.items():
        T |= v << (i * Bb)
    posO = lambda l: l if l > 0 else Wo - l                    # original numbering (fr_cnf)
    posR = lambda l: new[l] if l > 0 else W + new[-l]          # renamed numbering
    os.makedirs(a.outdir, exist_ok=True)
    mod = a.outdir.rstrip('/').replace('/', '.')
    sha = hashlib.sha256(open(a.cnf, 'rb').read()).hexdigest()
    hdr = 'set_option maxRecDepth 100000\nset_option Elab.async false\n'
    # ---- inputs
    chunks = [used[i:i + a.chunk] for i in range(0, len(used), a.chunk)]
    chunk_of = {}
    for k, ch in enumerate(chunks):
        for i in ch:
            chunk_of[i] = k
    usha = hashlib.sha256(''.join(' '.join(map(str, cls[i - 1])) + ' 0\n' for i in used).encode()).hexdigest()
    s = f'import FastRupCmd\n{hdr}namespace {a.ns}\nopen WinCNF\n'
    s += (f'/-! The {len(used)} clauses (of {ncl}) of `{os.path.basename(a.cnf)}` (sha256 {sha}) used by the LRAT\n'
          f'proof, in original order (sha256 of their DIMACS lines: {usha}).  `fr_cnf` records are\n'
          f'`index literal-positions… 0` with stride {Wo} (`v` ↦ v, `-v` ↦ {Wo} + v). -/\n')
    s += f'fr_cnf {Wo} {a.chunk}\n'
    s += '\n'.join(f'{i} ' + ' '.join(str(posO(l)) for l in cls[i - 1]) + ' 0' for i in used) + '\n'
    s += f'/-- The used input clauses. -/\nnoncomputable def F : CNF := {balanced([f"G{k}" for k in range(len(chunks))])}\n'
    s += 'def Inp (τ : Nat → Bool) : Prop := ∀ c ∈ F, clauseSat τ c\n'
    s += f'/-- Renaming table: entry `i` ({Bb} bits) is the original variable of checker variable `i`. -/\n'
    s += f'def RT : Nat := {hex(T)}\n'
    for k, ch in enumerate(chunks):
        s += f'fr_chunk {k} {W} {Bb} ' + ' '.join(str(new[abs(l)]) for i in ch for l in cls[i - 1]) + '\n'
    s += f'end {a.ns}\n'
    open(f'{a.outdir}/Inputs.lean', 'w').write(s)
    # ---- blocks
    blocks, cur, ch = [], [], 0
    for st in steps:
        cur.append(st); ch += len(st[2])
        if ch >= a.block_hints:
            blocks.append(cur); cur, ch = [], 0
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
    prev = f'{mod}.Inputs'
    names = [f'{a.outdir}/Inputs.lean']
    H = 0
    for m, bl in enumerate(mods):
        s = f'import {prev}\n{hdr}namespace {a.ns}\n'
        for b in bl:
            blk = blocks[b - 1]
            ext = {h for _, _, hs in blk for h in hs if h <= ncl or home[h] != b}
            rch = sorted({chunk_of[h] for h in ext if h <= ncl})
            rbl = sorted({home[h] for h in ext if h > ncl})
            slot, n = {}, 0
            for k in rch:
                for i in chunks[k]:
                    slot[i] = n; n += 1
            for rb in rbl:
                for e in exp_order[rb]:
                    slot[e] = n; n += 1
            for sid, _, _ in blk:
                slot[sid] = n; n += 1
            provs = [2 * k + 1 for k in rch] + [2 * rb for rb in rbl]
            data = [len(exp_order[b])] + [slot[e] for e in exp_order[b]] + [len(provs)] + provs
            s += f'-- block {b}: LRAT steps {blk[0][0]}..{blk[-1][0]}\nfr_block B{b} {W} {Bb} ' + ' '.join(map(str, data)) + '\n'
            for sid, c, hs in blk:
                H += len(hs)
                s += f'{sid} ' + ' '.join(str(posR(l)) for l in c) + (' 0 ' if c else '0 ') + ' '.join(str(slot[h] + 1) for h in hs) + ' 0\n'
        s += f'end {a.ns}\n'
        name = f'S{m:02d}'
        open(f'{a.outdir}/{name}.lean', 'w').write(s)
        names.append(f'{a.outdir}/{name}.lean')
        prev = f'{mod}.{name}'
    s = f'import {prev}\nopen WinCNF\n'
    s += (f'/-- `{a.ns}.F` is unsatisfiable: {len(steps)} RUP steps, {H} hints, {len(blocks)} kernel-checked blocks. -/\n'
          f'theorem {a.ns}_unsat : unsat {a.ns}.F :=\n  fun τ hF => {a.ns}.B{len(blocks)} τ hF False FastRup.msat_zero\n')
    open(f'{a.outdir}/Main.lean', 'w').write(s)
    names.append(f'{a.outdir}/Main.lean')
    print(f'inputs {len(used)} chunks {len(chunks)} steps {len(steps)} hints {H} blocks {len(blocks)} '
          f'modules {len(mods)} vars {nv} -> {W - 1}', file=sys.stderr)
    print(' '.join(names))


if __name__ == '__main__':
    main()
