#!/usr/bin/env python3
"""Low-memory twin of milestones/26-replay-efficiency/scripts/gen_lean_lrat_v3.py (checker v3 replay
source), for proofs of ~100 M hints, where the original holds every hint as a Python object (OOM at
12.8 GB on a 15 GB machine for 92.6 M hints).

    genv3stream.py --work DIR --data COREDIR --out ROOT [--seg N] [--off OFF] [--max-lemmas N]
                   [--pack-chunk B] [--warm W] NAME

Same arguments and the SAME output bytes as gen_lean_lrat_v3.py (no --check): it imports that script's
ppack / tpack / pack / warm_blocks and repeats its `export` loop segment by segment, reading the LRAT
file three times (sizes and cuts; tables and word width; words) and keeping only per-lemma ids,
offsets and the lemma -> (segment, index) map in memory. The equality of the output is tested on
smaller certificates (--compare runs the original too and compares the files).
"""
import argparse, json, os, sys
from array import array

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '26-replay-efficiency', 'scripts'))
sys.dont_write_bytecode = True
import gen_lean_lrat_v3 as V   # noqa: E402
G = V.G


def parse(line):
    t = [int(x) for x in line.split()]
    z = t.index(0, 1)
    hints = t[z + 1:-1]
    assert t[-1] == 0 and all(h > 0 for h in hints), 'RAT hints are not supported'
    return t[0], t[1:z], hints


class Seg:
    """lemmas[j] for j in one segment, read from the LRAT file."""
    def __init__(self, path, offs, a, b):
        self.a = a
        self.items = []
        with open(path, 'rb') as f:
            f.seek(offs[a])
            while len(self.items) < b - a:
                line = f.readline()
                t = line.split()
                if t[1] == b'd':
                    continue
                self.items.append(parse(line))

    def __getitem__(self, j):
        return self.items[j - self.a]


def export(name, work, data, outroot, seg_hints, OFF, chunk=16384, wmin=13, max_lemmas=4000, warm=0):
    meta = json.load(open(os.path.join(data, name + '.json')))
    mod = meta['module'].split('.')[-1]
    core_ids = meta['core_ids']
    path = os.path.join(work, name + '.lrat')
    # pass 1: ids, offsets, hint counts
    ids, offs, nhs = array('q'), array('q'), array('i')
    last_lits = None
    with open(path, 'rb') as f:
        pos = 0
        for line in f:
            t = line.split()
            if t[1] != b'd':
                z = t.index(b'0', 1)
                ids.append(int(t[0]))
                offs.append(pos)
                nhs.append(len(t) - z - 2)
                last_lits = z - 1
            pos += len(line)
    n = len(ids)
    assert last_lits == 0, 'last lemma must be the empty clause'
    raw_idx = {c: i for i, c in enumerate(core_ids)}
    cuts, acc = [0], 0
    for i in range(n):
        acc += nhs[i]
        if (acc >= seg_hints or i + 1 - cuts[-1] >= max_lemmas) and i + 1 < n:
            cuts.append(i + 1)
            acc = 0
    cuts.append(n)
    nseg = len(cuts) - 1
    assert nseg < 4095, 'too many segments for the 12-bit segment field of a reference'
    where = {}
    for c in range(nseg):
        for j in range(cuts[c], cuts[c + 1]):
            where[ids[j]] = (c, j - cuts[c])
    total_hints = sum(nhs)
    del nhs

    def bit(l):
        v = abs(l)
        assert 0 < v < OFF
        return v if l > 0 else v + OFF

    def segment(c, lemmas):
        table, pos = [0], {}
        lw = []
        maxlocal = maxlit = 0
        for j in range(cuts[c], cuts[c + 1]):
            cid, lits, hints = lemmas[j]
            ws = []
            for h in hints:
                if h in where and where[h][0] == c:
                    jj = where[h][1]
                    assert jj < j - cuts[c]
                    ws.append(('L', jj + 1))
                    maxlocal = max(maxlocal, jj + 1)
                else:
                    if h in where:
                        s, jj = where[h]
                        assert s < c
                        r = (jj << 12) | (s + 1)
                    else:
                        r = raw_idx[h] << 12
                    if r not in pos:
                        pos[r] = len(table)
                        table.append(r)
                    ws.append(('T', pos[r]))
            assert len(hints) < V.HINT_FUEL - 1
            maxlit = max([maxlit, len(lits)] + [bit(l) for l in lits])
            lw.append((lits, ws))
        return table, lw, maxlocal, maxlit
    # pass 2: word width
    maxlocal, maxent, maxlit, ntab = 0, 0, 0, 0
    for c in range(nseg):
        table, _, ml, mt = segment(c, Seg(path, offs, cuts[c], cuts[c + 1]))
        maxlocal, maxlit = max(maxlocal, ml), max(maxlit, mt)
        maxent = max(maxent, len(table) - 1)
        ntab += len(table) - 1
    W = wmin
    while not ((1 << W) - 1 >= maxlit and maxlocal < (1 << (W - 1)) and maxent <= (1 << (W - 1)) - 1):
        W += 1
    M, FLAG = (1 << W) - 1, 1 << (W - 1)
    stats = dict(name=name, module=mod, lemmas=n, hints=total_hints, segments=nseg, wbits=W, off=OFF,
                 table_entries=ntab, max_local=maxlocal, max_entry=maxent)
    ns = 'Snake9.LocalWindow.' + mod
    os.makedirs(os.path.join(outroot, 'LocalWindowUnsat'), exist_ok=True)
    p = os.path.join(outroot, 'LocalWindowUnsat', mod + '.lean')
    tp = p + '.tables.tmp'
    out, tout = open(p + '.tmp', 'w'), open(tp, 'w')
    H = ['import LratV3', 'import LocalWindowCnf.' + mod, 'import ProofPack', '',
         '/-! Kernel-checked LRAT refutation of the core of `%s` for the checker v3: %d lemmas, %d hints, '
         '%d segments\n(generated by `milestones/26-replay-efficiency/scripts/gen_lean_lrat_v3.py`). -/' % (name, stats['lemmas'], stats['hints'], nseg), '',
         'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option Elab.async false', '',
         'namespace ' + ns, '']
    for e in H:
        out.write(e + '\n')
    args = '%d %d %d %d raw Ps' % (OFF, W, M, FLAG)
    tail, nwarm = [], 0
    for c in range(nseg):
        lemmas = Seg(path, offs, cuts[c], cuts[c + 1])
        table, lw, _, _ = segment(c, lemmas)
        ws_all = []
        for lits, ws in lw:
            words = [len(lits)] + [bit(l) for l in lits] + [(FLAG + v) if k == 'T' else v for k, v in ws] + [0]
            ws_all.append(V.pack(words, W))
        out.write('noncomputable def p%d : List Nat := Snake9.ProofPack.unpackL %d [\n%s]' %
                  (c, W, ',\n'.join('  nat_lit 0x%x' % x for x in V.ppack(ws_all, W, chunk))) + '\n\n')
        tout.write('noncomputable def t%d : List Nat := [\n%s]' %
                   (c, ',\n'.join('  nat_lit 0x%x' % x for x in V.tpack(table))) + '\n\n')
        # ok / warm (same text as gen_lean_lrat_v3)
        if c < nseg - 1:
            stmt = 'Snake9.LratV3.check %s t%d %d' % (args, c, c)
        else:
            stmt = 'Snake9.LratV3.andB (Snake9.LratV3.check %s t%d %d) (Snake9.LratV3.hasEmpty %d %d (Snake9.LratV3.segP Ps %d))' % (
                args, c, c, W, M, c)
        wb = V.warm_blocks(lemmas, cuts, where, raw_idx, c, warm)
        if not wb:
            tail += ['theorem ok%d : %s = true := by' % (c, stmt), '  decide +kernel', '']
            continue
        nwarm += len(wb)
        ws_ = []
        for key, b in wb:
            if key == 'R':
                x = 'Snake9.LratV3.headR %d (Snake9.LratV3.nthR raw %d)' % (OFF, 64 * b)
            else:
                x = 'Snake9.LratV3.headL %d %d %d (Snake9.LratV3.nthN (Snake9.LratV3.segP Ps %d) %d)' % (OFF, W, M, key, 64 * b)
            ws_.append('Snake9.LratV3.seqN (%s) true' % x)
        wt = 'true'
        for x in reversed(ws_):
            wt = 'Snake9.LratV3.andB (%s)\n    (%s)' % (x, wt)
        tail += ['theorem warm%d : Snake9.LratV3.andB\n    (%s)\n    (%s) = true := by' % (c, wt, stmt), '  decide +kernel', '',
                 'theorem ok%d : %s = true := (Snake9.LratV3.andB_eq_true warm%d).2' % (c, stmt, c), '']
    stats['warm_blocks'] = nwarm
    tout.close()
    out.write('noncomputable def Ps : List (List Nat) := [%s]' % ', '.join('p%d' % c for c in range(nseg)) + '\n\n')
    with open(tp) as f:
        for blk in iter(lambda: f.read(1 << 24), ''):
            out.write(blk)
    os.remove(tp)
    L = tail
    L += ['theorem unsat : Unsat cnf := by', '  apply Snake9.LratV3.unsat_of_raw', '  intro τ h',
          '  have hoff : 0 < %d := by decide' % OFF,
          '  have hr : Snake9.LratV3.RawTrue %d τ raw := Snake9.LratV3.rawTrue_of_cnf hoff h' % OFF,
          '  have h0 : Snake9.LratV3.SegsTrue %d %d %d τ Ps 0 := Snake9.LratV3.segsTrue_zero _ _ _ τ Ps' % (OFF, W, M)]
    st = 'Snake9.LratV3.SegsTrue %d %d %d τ Ps' % (OFF, W, M)
    if nseg - 1 <= V.MAIN_CHUNK:
        for c in range(nseg - 1):
            L.append('  have h%d : %s %d := Snake9.LratV3.seg_step hoff hr ok%d h%d' % (c + 1, st, c + 1, c, c))
    else:
        thm = L.index('theorem unsat : Unsat cnf := by')
        lem = []
        for a in range(0, nseg - 1, V.MAIN_CHUNK):
            b = min(a + V.MAIN_CHUNK, nseg - 1)
            lem += ['theorem steps%d (τ : Nat → Bool) (hoff : 0 < %d) (hr : Snake9.LratV3.RawTrue %d τ raw) (h%d : %s %d) : %s %d := by'
                    % (a, OFF, OFF, a, st, a, st, b)]
            lem += ['  have h%d : %s %d := Snake9.LratV3.seg_step hoff hr ok%d h%d' % (c + 1, st, c + 1, c, c) for c in range(a, b)]
            lem += ['  exact h%d' % b, '']
            L.append('  have h%d : %s %d := steps%d τ hoff hr h%d' % (b, st, b, a, a))
        L[thm:thm] = lem
    L += ['  exact Snake9.LratV3.final_false hoff hr ok%d h%d' % (nseg - 1, nseg - 1), '', 'end ' + ns, '']
    out.write('\n'.join(L))
    out.close()
    os.replace(p + '.tmp', p)
    stats['lean_bytes'] = len(open(p, encoding='utf-8').read())   # characters, as the original
    return stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', required=True)
    ap.add_argument('--data', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--seg', type=int, default=60000)
    ap.add_argument('--off', type=int, default=4000)
    ap.add_argument('--max-lemmas', type=int, default=4000)
    ap.add_argument('--pack-chunk', type=int, default=16384)
    ap.add_argument('--warm', type=int, default=0)
    ap.add_argument('names', nargs='+')
    a = ap.parse_args()
    for n in a.names:
        print(json.dumps(export(n, a.work, a.data, a.out, a.seg, a.off, a.pack_chunk,
                                max_lemmas=a.max_lemmas, warm=a.warm)), flush=True)


if __name__ == '__main__':
    main()
