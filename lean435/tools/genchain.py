#!/usr/bin/env python3
"""Segmented (checkpoint) checker-v3 replay source: genv3stream.py's output, cut into pieces.

    genchain.py --work DIR --data COREDIR --out ROOT --piece-hints H [--seg N] [--off OFF] [--max-lemmas N] NAME

Reads the compacted LRAT `WORK/NAME.lrat` and `COREDIR/NAME.json` (pilot.py output), as genv3stream.py.
The lemmas are cut into pieces of about H hints (proof order); each piece is cut into segments as in
genv3stream.py. For a cut before piece i the boundary B_i is the list of lemmas of earlier pieces that some
piece >= i cites, in proof order, chunked into segments of at most --max-lemmas words (`n lits 0`, no
hints). Writes, under ROOT (plain Lean modules; see milestones/39-dim8-lift/lean/LratChain.lean):

  LocalWindowChain/MOD/B<i>.lean   def B : List (List Nat)                (boundary i >= 1, packed words)
  LocalWindowChain/MOD/P<i>.lean   own segment data, tables, Ps := B_i.B ++ own, ok<c> checks and
                                   theorem piece (non-last: SegsTrue of B_{i+1}, by coverChk)
                                                  (last: False, by final_false)
  LocalWindowUnsat/MOD.lean        theorem unsat : Unsat cnf   (chains the pieces; same statement as
                                   genv3stream.py's module)
and prints a JSON summary (pieces, per-piece lemmas / hints / segments / |B_i|, word width).
"""
import argparse, json, os, sys
from array import array

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '26-replay-efficiency', 'scripts'))
sys.dont_write_bytecode = True
import gen_lean_lrat_v3 as V   # noqa: E402


def parse(line):
    t = [int(x) for x in line.split()]
    z = t.index(0, 1)
    hints = t[z + 1:-1]
    assert t[-1] == 0 and all(h > 0 for h in hints), 'RAT hints are not supported'
    return t[0], t[1:z], hints


def read_range(path, offs, a, b):
    """lemmas a..b-1 (indices into the non-deletion lines)"""
    out = []
    if a >= b:
        return out
    with open(path, 'rb') as f:
        f.seek(offs[a])
        while len(out) < b - a:
            line = f.readline()
            if line.split()[1] == b'd':
                continue
            out.append(parse(line))
    return out


def export(name, work, data, outroot, piece_hints, seg_hints, OFF, chunk=16384, wmin=13, max_lemmas=4000):
    meta = json.load(open(os.path.join(data, name + '.json')))
    mod = meta['module'].split('.')[-1]
    raw_idx = {c: i for i, c in enumerate(meta['core_ids'])}
    path = os.path.join(work, name + '.lrat')
    # pass 1: ids, offsets, hint counts, literal counts
    ids, offs, nhs = array('q'), array('q'), array('i')
    with open(path, 'rb') as f:
        pos = 0
        for line in f:
            t = line.split()
            if t[1] != b'd':
                z = t.index(b'0', 1)
                ids.append(int(t[0])); offs.append(pos); nhs.append(len(t) - z - 2)
                last_lits = z - 1
            pos += len(line)
    n = len(ids)
    assert last_lits == 0, 'last lemma must be the empty clause'
    index = {x: i for i, x in enumerate(ids)}
    # pieces (by hints) and, inside each, segments (as genv3stream.py)
    pcut, acc = [0], 0
    for i in range(n):
        acc += nhs[i]
        if acc >= piece_hints and i + 1 < n:
            pcut.append(i + 1); acc = 0
    pcut.append(n)
    K = len(pcut) - 1
    piece = array('i', [0]) * n
    for p in range(K):
        for i in range(pcut[p], pcut[p + 1]):
            piece[i] = p
    scuts = []   # per piece: segment cut list (absolute lemma indices)
    for p in range(K):
        cs, acc = [pcut[p]], 0
        for i in range(pcut[p], pcut[p + 1]):
            acc += nhs[i]
            if (acc >= seg_hints or i + 1 - cs[-1] >= max_lemmas) and i + 1 < pcut[p + 1]:
                cs.append(i + 1); acc = 0
        cs.append(pcut[p + 1])
        scuts.append(cs)
    # pass 2: last citing piece of every lemma
    last = array('i', [-1]) * n
    with open(path, 'rb') as f:
        i = 0
        for line in f:
            t = line.split()
            if t[1] == b'd':
                continue
            z = t.index(b'0', 1); q = piece[i]
            for h in t[z + 1:-1]:
                j = index.get(int(h))
                if j is not None and piece[j] < q and last[j] < q:
                    last[j] = q
            i += 1
    # boundaries: B[p] = sorted lemma indices j with piece[j] < p <= last[j]
    B = [[] for _ in range(K + 1)]
    for j in range(n):
        for p in range(piece[j] + 1, last[j] + 1):
            B[p].append(j)
    bchunks = [[] for _ in range(K + 1)]   # filled below, piece by piece (chunks follow origin segments)

    def bit(l):
        v = abs(l)
        assert 0 < v < OFF
        return v if l > 0 else v + OFF

    def where_of(p):
        """lemma id -> (virtual segment, index) for piece p: boundary chunks first, then own segments"""
        w = {}
        for s, ch in enumerate(bchunks[p]):
            for jj, j in enumerate(ch):
                w[ids[j]] = (s, jj)
        nb = len(bchunks[p])
        for c in range(len(scuts[p]) - 1):
            for j in range(scuts[p][c], scuts[p][c + 1]):
                w[ids[j]] = (nb + c, j - scuts[p][c])
        return w

    # boundary chunks: B[p] in proof order, cut where the origin (virtual segment of piece p - 1 holding the
    # lemma) changes and at max_lemmas words, so that each export check of piece p - 1 decodes one segment
    # Lemmas passed through from boundary B[p - 1] share one key (their chunks are small; one check may decode
    # several), so the boundary does not fragment from piece to piece.
    for p in range(1, K):
        w = where_of(p - 1); nbp = len(bchunks[p - 1]); chs, cur, key = [], [], None
        for j in B[p]:
            k_ = w[ids[j]][0]
            if k_ < nbp: k_ = -1
            if cur and (k_ != key or len(cur) >= max_lemmas):
                chs.append(cur); cur = []
            cur.append(j); key = k_
        if cur: chs.append(cur)
        bchunks[p] = chs

    def segment(p, c, lemmas, where):
        """own segment c (virtual index nb + c) of piece p: table and words"""
        nb = len(bchunks[p]); vc = nb + c
        table, posd, lw = [0], {}, []
        maxlocal = maxlit = 0
        a = scuts[p][c]
        for k, (cid, lits, hints) in enumerate(lemmas):
            ws = []
            for h in hints:
                if h in where and where[h][0] == vc:
                    jj = where[h][1]; assert jj < k
                    ws.append(('L', jj + 1)); maxlocal = max(maxlocal, jj + 1)
                else:
                    if h in where:
                        s, jj = where[h]; assert s < vc, (h, s, vc)
                        r = (jj << 12) | (s + 1)
                    else:
                        assert h not in index, 'lemma %d cited across pieces but not in the boundary' % h
                        r = raw_idx[h] << 12
                    if r not in posd:
                        posd[r] = len(table); table.append(r)
                    ws.append(('T', posd[r]))
            assert len(hints) < V.HINT_FUEL - 1
            maxlit = max([maxlit, len(lits)] + [bit(l) for l in lits])
            lw.append((lits, ws))
        return table, lw, maxlocal, maxlit

    # pass 3: global word width (one W for all pieces: boundary words travel between them)
    maxlocal = maxent = maxlit = 0
    for p in range(K):
        where = where_of(p)
        for c in range(len(scuts[p]) - 1):
            table, _, ml, mt = segment(p, c, read_range(path, offs, scuts[p][c], scuts[p][c + 1]), where)
            maxlocal, maxlit, maxent = max(maxlocal, ml), max(maxlit, mt), max(maxent, len(table) - 1)
        nseg = len(bchunks[p]) + len(scuts[p]) - 1
        assert nseg < 4095, 'too many segments in piece %d' % p
    W = wmin
    while not ((1 << W) - 1 >= maxlit and maxlocal < (1 << (W - 1)) and maxent <= (1 << (W - 1)) - 1):
        W += 1
    M, FLAG = (1 << W) - 1, 1 << (W - 1)
    ns = 'Snake9.LocalWindow.' + mod
    cdir = os.path.join(outroot, 'LocalWindowChain', mod)
    os.makedirs(cdir, exist_ok=True); os.makedirs(os.path.join(outroot, 'LocalWindowUnsat'), exist_ok=True)
    HDR = ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option Elab.async false', '']
    st = 'Snake9.LratV3.SegsTrue %d %d %d' % (OFF, W, M)
    # boundary modules B1..B(K-1)
    lemcache = {}
    for p in range(1, K):
        js = [j for ch in bchunks[p] for j in ch]
        lem = {}
        for j in js:
            if j not in lemcache:
                lemcache[j] = read_range(path, offs, j, j + 1)[0][1]
            lem[j] = lemcache[j]
        with open(os.path.join(cdir, 'B%d.lean' % p), 'w') as o:
            o.write('import ProofPack\n\n' + '\n'.join(HDR) + '\nnamespace %s.Chain.B%d\n\n' % (ns, p))
            for s, ch in enumerate(bchunks[p]):
                ws = [V.pack([len(lem[j])] + [bit(l) for l in lem[j]] + [0], W) for j in ch]
                o.write('noncomputable def b%d : List Nat := Snake9.ProofPack.unpackL %d [\n%s]\n\n' %
                        (s, W, ',\n'.join('  nat_lit 0x%x' % x for x in V.ppack(ws, W, chunk))))
            o.write('noncomputable def B : List (List Nat) := [%s]\n\nend %s.Chain.B%d\n' %
                    (', '.join('b%d' % s for s in range(len(bchunks[p]))), ns, p))
        # free memory of lemmas not needed by later boundaries
        for j in list(lemcache):
            if last[j] <= p:
                del lemcache[j]
    # piece modules
    summary = []
    for p in range(K):
        where = where_of(p); nb = len(bchunks[p]); nown = len(scuts[p]) - 1; n_all = nb + nown
        lastp = p == K - 1
        imp = ['import LratChain', 'import LocalWindowCnf.' + mod, 'import ProofPack']
        if p >= 1: imp.append('import LocalWindowChain.%s.B%d' % (mod, p))
        if not lastp: imp.append('import LocalWindowChain.%s.B%d' % (mod, p + 1))
        P = os.path.join(cdir, 'P%d.lean' % p)
        o = open(P + '.tmp', 'w')
        o.write('\n'.join(imp) + '\n\n/-! Piece %d of %d of the segmented replay of `%s`. -/\n\n' % (p, K, name) + '\n'.join(HDR))
        o.write('\nnamespace %s.Chain.P%d\nopen %s\n\n' % (ns, p, ns))
        args = '%d %d %d %d raw Ps' % (OFF, W, M, FLAG)
        oks = []; hints_p = 0
        for c in range(nown):
            lemmas = read_range(path, offs, scuts[p][c], scuts[p][c + 1])
            hints_p += sum(len(x[2]) for x in lemmas)
            table, lw, _, _ = segment(p, c, lemmas, where)
            ws_all = [V.pack([len(lits)] + [bit(l) for l in lits] + [(FLAG + v) if k == 'T' else v for k, v in ws] + [0], W)
                      for lits, ws in lw]
            o.write('noncomputable def p%d : List Nat := Snake9.ProofPack.unpackL %d [\n%s]\n\n' %
                    (c, W, ',\n'.join('  nat_lit 0x%x' % x for x in V.ppack(ws_all, W, chunk))))
            o.write('noncomputable def t%d : List Nat := [\n%s]\n\n' % (c, ',\n'.join('  nat_lit 0x%x' % x for x in V.tpack(table))))
            vc = nb + c
            if lastp and c == nown - 1:
                stmt = 'Snake9.LratV3.andB (Snake9.LratV3.check %s t%d %d) (Snake9.LratV3.hasEmpty %d %d (Snake9.LratV3.segP Ps %d))' % (args, c, vc, W, M, vc)
            else:
                stmt = 'Snake9.LratV3.check %s t%d %d' % (args, c, vc)
            oks.append('theorem ok%d : %s = true := by\n  decide +kernel\n' % (vc, stmt))
        bref = 'LocalWindowChain.%s.B%d' % (mod, p)
        bterm = '%s.Chain.B%d.B' % (ns, p) if p >= 1 else '([] : List (List Nat))'
        o.write('noncomputable def own : List (List Nat) := [%s]\n\n' % ', '.join('p%d' % c for c in range(nown)))
        o.write('noncomputable def Ps : List (List Nat) := %s ++ own\n\n' % bterm)
        o.write('\n'.join(oks) + '\n')
        if not lastp:
            # references for the next boundary, chunk by chunk
            refs = []
            for ch in bchunks[p + 1]:
                rr, segs = [], set()
                for j in ch:
                    s, jj = where[ids[j]]
                    rr.append((jj << 12) | (s + 1)); segs.add(s)
                # chunks of own lemmas of piece p point into one own segment; only pass-through chunks
                # (lemmas of B[p]) may span several boundary segments
                assert len(segs) == 1 or max(segs) < nb, (p, sorted(segs)[:5])
                refs.append(rr)
            # one reference list per boundary chunk, as 500-element sub-lists joined by ++ (a 4,000-element
            # list literal exceeds maxRecDepth when elaborated; the value is the same), and one check per
            # chunk: a chunk of own lemmas points into one own segment of Ps, so its check decodes only that
            # segment (a pass-through chunk may decode several boundary segments, which are small)
            nxt = '%s.Chain.B%d' % (ns, p + 1)
            for s, rr in enumerate(refs):
                sub = [rr[a:a + 500] for a in range(0, len(rr), 500)] or [[]]
                for i_, x_ in enumerate(sub):
                    o.write('def r%d_%d : List Nat := [%s]\n' % (s, i_, ', '.join(map(str, x_))))
                o.write('def r%d : List Nat := %s\n\n' % (s, ' ++ '.join('r%d_%d' % (s, i_) for i_ in range(len(sub)))))
                o.write('theorem ox%d : Snake9.LratChain.zipChk %d %d %d raw Ps %d %s.b%d r%d = true := by\n  decide +kernel\n\n'
                        % (s, OFF, W, M, n_all, nxt, s, s))
        L = ['theorem piece (τ : Nat → Bool) (hoff : 0 < %d) (hr : Snake9.LratV3.RawTrue %d τ raw)' % (OFF, OFF)]
        L[0] += (' (hB : %s τ %s %s.length) :' % (st, bterm, bterm)) if p >= 1 else ' :'
        L[0] += (' %s τ %s.Chain.B%d.B %s.Chain.B%d.B.length := by' % (st, ns, p + 1, ns, p + 1)) if not lastp else ' False := by'
        if p >= 1:
            L += ['  have hb : %s τ Ps %d := by' % (st, nb),
                  '    have h := Snake9.LratChain.segsTrue_append %s own hB' % bterm,
                  '    have hl : (%s).length = %d := rfl' % (bterm, nb),
                  '    rw [hl] at h; exact h']
        else:
            L += ['  have hb : %s τ Ps 0 := Snake9.LratV3.segsTrue_zero _ _ _ τ Ps' % st]
        prev = 'hb'
        for c in range(nown - (1 if lastp else 0)):
            vc = nb + c
            L.append('  have h%d : %s τ Ps %d := Snake9.LratV3.seg_step hoff hr ok%d %s' % (vc + 1, st, vc + 1, vc, prev))
            prev = 'h%d' % (vc + 1)
        if lastp:
            L.append('  exact Snake9.LratV3.final_false hoff hr ok%d %s' % (n_all - 1, prev))
        else:
            nb1 = len(bchunks[p + 1]); nxt = '%s.Chain.B%d' % (ns, p + 1)
            L.append('  show %s τ [%s] [%s].length' % (st, ', '.join('%s.b%d' % (nxt, s) for s in range(nb1)),
                                                      ', '.join('%s.b%d' % (nxt, s) for s in range(nb1))))
            term = 'Snake9.LratChain.segsTrue_nil _ _ _ τ'
            for s in reversed(range(nb1)):
                term = 'Snake9.LratChain.segsTrue_cons (Snake9.LratChain.zipChk_sound hoff hr %s _ _ ox%d)\n    (%s)' % (prev, s, term)
            L.append('  exact ' + term)
        o.write('\n'.join(L) + '\n\nend %s.Chain.P%d\n' % (ns, p))
        o.close(); os.replace(P + '.tmp', P)
        summary.append(dict(piece=p, lemmas=pcut[p + 1] - pcut[p], hints=hints_p, own_segments=nown,
                            boundary_in=len(B[p]), boundary_segments=nb))
    # top module
    T = ['import LratChain', 'import LocalWindowCnf.' + mod] + ['import LocalWindowChain.%s.P%d' % (mod, p) for p in range(K)]
    T += ['', '/-! Kernel-checked LRAT refutation of the core of `%s`, segmented into %d pieces (genchain.py). -/' % (name, K), '']
    T += HDR + ['namespace ' + ns, '', 'theorem unsat : Unsat cnf := by', '  apply Snake9.LratV3.unsat_of_raw', '  intro τ h',
                '  have hoff : 0 < %d := by decide' % OFF,
                '  have hr : Snake9.LratV3.RawTrue %d τ raw := Snake9.LratV3.rawTrue_of_cnf hoff h' % OFF]
    for p in range(K - 1):
        T.append('  have b%d := %s.Chain.P%d.piece τ hoff hr%s' % (p + 1, ns, p, ' b%d' % p if p >= 1 else ''))
    T.append('  exact %s.Chain.P%d.piece τ hoff hr%s' % (ns, K - 1, ' b%d' % (K - 1) if K >= 2 else ''))
    T += ['', 'end ' + ns, '']
    open(os.path.join(outroot, 'LocalWindowUnsat', mod + '.lean'), 'w').write('\n'.join(T))
    modules = ['LocalWindowChain/%s/B%d' % (mod, p) for p in range(1, K)] + \
              ['LocalWindowChain/%s/P%d' % (mod, p) for p in range(K)] + ['LocalWindowUnsat/' + mod]
    return dict(name=name, module=mod, lemmas=n, hints=int(sum(nhs)), pieces=K, wbits=W, off=OFF,
                max_boundary=max(len(b) for b in B), modules=modules, per_piece=summary)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', required=True); ap.add_argument('--data', required=True); ap.add_argument('--out', required=True)
    ap.add_argument('--piece-hints', type=int, required=True)
    ap.add_argument('--seg', type=int, default=60000); ap.add_argument('--off', type=int, default=4000)
    ap.add_argument('--max-lemmas', type=int, default=4000); ap.add_argument('--pack-chunk', type=int, default=16384)
    ap.add_argument('names', nargs='+')
    a = ap.parse_args()
    for nm in a.names:
        print(json.dumps(export(nm, a.work, a.data, a.out, a.piece_hints, a.seg, a.off, a.pack_chunk,
                                max_lemmas=a.max_lemmas)), flush=True)


if __name__ == '__main__':
    main()
