"""Emit a kernel-checked LRAT refutation for the checker v3 (work/final_lean/LratV3.lean).

  python gen_lean_lrat_v3.py --work DIR --data COREDIR --out ROOT [--seg N] [--off OFF] [--check] NAME ...

The replay modules this writes replace those of `gen_lean_lrat.py --fast --split --packed` (same
module name `LocalWindowUnsat.<Module>`, same theorem `Snake9.LocalWindow.<Module>.unsat : Unsat cnf`)
and are about 1.4-1.65x faster in the kernel; see milestones/26-replay-efficiency/README.md,
"Checker v3".  `replay_k7.py gen --checker v3` calls this script.

Reads NAME.lrat and NAME.cnf from --work and the core JSON NAME.json from --data (as
gen_lean_lrat.py) and writes ROOT/LocalWindowUnsat/<Module>.lean, one module:

* proof segments `p<c>` of about --seg hints, `Snake9.ProofPack.unpackL W [...]` of lemma words
  `n lit_1 ... lit_n hint ... hint 0` (W-bit words, lowest first; a literal word is its bit);
* `Ps := [p0, p1, ...]`;
* per segment a reference table `t<c>`: a list of chunks `tw + 2^6 st` of 1024 fields of `tw`
  bits (`fieldT`); entry 0 is unused, entry e is a reference `idx << 12 | seg` (seg 0: input
  clause idx of `raw`; seg s >= 1: lemma idx of segment s - 1);
* hint words: FLAG + e for table entry e, j + 1 for lemma j of the current segment, 0 at the end;
* `ok<c> : check OFF W M FLAG raw Ps t<c> c = true`, the last one with `hasEmpty`;
* `unsat : Unsat cnf` by `seg_step` / `final_false`.

With --check the Python mirror of `check` runs first (it accepts strictly less than the kernel).
"""
import argparse, json, os, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
S10 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')
sys.path.insert(0, S10)
import gen_lean_lrat as G          # noqa: E402  (read_cnf_core, read_lrat)

HINT_FUEL = 4095   # fuel of `hints` in LratV3.lean
MAIN_CHUNK = 500                   # segments per step lemma of the main theorem


def ppack(xs, W, cbytes):
    """ProofPack chunks of the words xs (ProofPack.lean)."""
    groups, cur, bits = [], [], 0
    for x in xs:
        b = 16 + W * -(-x.bit_length() // W)
        if cur and (bits + b > 8 * cbytes or len(cur) >= 65535):
            groups.append(cur)
            cur, bits = [], 0
        cur.append(x)
        bits += b
    if cur:
        groups.append(cur)
    out = []
    for g in groups:
        st, pos = 0, 0
        for x in g:
            n = -(-x.bit_length() // W)
            st |= (n | (x << 16)) << pos
            pos += 16 + W * n
        out.append(len(g) | (st << 16))
    # mirror of unpackL
    dec = []
    for c in out:
        n, st = c & 65535, c >> 16
        for _ in range(n):
            b = W * (st & 65535)
            dec.append((st >> 16) & ((1 << b) - 1))
            st >>= 16 + b
    assert dec == list(xs)
    return out


def tpack(xs):
    """Table chunks `tw + 2^6 st` of 1024 fields of `tw` bits (`LratV3.fieldT`)."""
    cs = []
    for i in range(0, len(xs), 1024):
        g = xs[i:i + 1024]
        tw = max(1, max(x.bit_length() for x in g))
        assert tw < 64
        st = 0
        for j, x in enumerate(g):
            st |= x << (j * tw)
        cs.append(tw | (st << 6))
    for e, x in enumerate(xs):   # mirror of lookE's field extraction
        ch = cs[e >> 10]
        assert (ch >> (6 + (e & 1023) * (ch & 63))) & ((1 << (ch & 63)) - 1) == x
    return cs


def pack(ws, W):
    x = 0
    for j, w in enumerate(ws):
        assert 0 <= w < (1 << W)
        x |= w << (W * j)
    return x


def export(name, work, data, outroot, seg_hints, OFF, check, chunk=16384, wmin=13, max_lemmas=4000):
    meta = json.load(open(os.path.join(data, name + '.json')))
    mod = meta['module'].split('.')[-1]
    core_ids = meta['core_ids']
    core_cls = G.read_cnf_core(os.path.join(work, name + '.cnf'), core_ids)
    lemmas = G.read_lrat(os.path.join(work, name + '.lrat'))
    assert lemmas[-1][1] == [], 'last lemma must be the empty clause'
    raw_idx = {c: i for i, c in enumerate(core_ids)}
    # segments
    cuts, acc = [0], 0
    for i, (_, _, hs) in enumerate(lemmas):
        acc += len(hs)
        if (acc >= seg_hints or i + 1 - cuts[-1] >= max_lemmas) and i + 1 < len(lemmas):
            cuts.append(i + 1)
            acc = 0
    cuts.append(len(lemmas))
    nseg = len(cuts) - 1
    assert nseg < 4095, 'too many segments for the 12-bit segment field of a reference'
    where = {}   # lemma id -> (segment, local index)
    for c in range(nseg):
        for j in range(cuts[c], cuts[c + 1]):
            where[lemmas[j][0]] = (c, j - cuts[c])

    def bit(l):
        v = abs(l)
        assert 0 < v < OFF
        return v if l > 0 else v + OFF
    # references, tables, words per segment
    segs = []
    maxlocal, maxent, maxlit = 0, 0, 0
    for c in range(nseg):
        table, pos = [0], {}
        lw = []
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
            assert len(hints) < HINT_FUEL - 1
            maxlit = max([maxlit, len(lits)] + [bit(l) for l in lits])
            lw.append((lits, ws))
        maxent = max(maxent, len(table) - 1)
        segs.append((table, lw))
    W = wmin
    while not ((1 << W) - 1 >= maxlit and maxlocal < (1 << (W - 1)) and maxent <= (1 << (W - 1)) - 1):
        W += 1
    M, FLAG = (1 << W) - 1, 1 << (W - 1)
    proofs = []
    for table, lw in segs:
        ws_all = []
        for lits, ws in lw:
            words = [len(lits)] + [bit(l) for l in lits] + [(FLAG + v) if k == 'T' else v for k, v in ws] + [0]
            ws_all.append(pack(words, W))
        proofs.append(ws_all)
    stats = dict(name=name, module=mod, lemmas=len(lemmas), hints=sum(len(h) for _, _, h in lemmas),
                 segments=nseg, wbits=W, off=OFF, table_entries=sum(len(t) - 1 for t, _ in segs),
                 max_local=maxlocal, max_entry=maxent)
    if check:
        simulate(core_cls, proofs, [t for t, _ in segs], OFF, W)
        stats['simulated'] = True
    # ---- Lean
    ns = 'Snake9.LocalWindow.' + mod   # checker names are qualified: the Cnf module has its own `check`
    L = ['import LratV3', 'import LocalWindowCnf.' + mod, 'import ProofPack', '',
         '/-! Kernel-checked LRAT refutation of the core of `%s` for the checker v3: %d lemmas, %d hints, '
         '%d segments\n(generated by `milestones/26-replay-efficiency/scripts/gen_lean_lrat_v3.py`). -/' % (name, stats['lemmas'], stats['hints'], nseg), '',
         'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option Elab.async false', '',
         'namespace ' + ns, '']
    for c, ws in enumerate(proofs):
        L += ['noncomputable def p%d : List Nat := Snake9.ProofPack.unpackL %d [\n%s]' %
              (c, W, ',\n'.join('  nat_lit 0x%x' % x for x in ppack(ws, W, chunk))), '']
    L += ['noncomputable def Ps : List (List Nat) := [%s]' % ', '.join('p%d' % c for c in range(nseg)), '']
    for c, (table, _) in enumerate(segs):
        L += ['noncomputable def t%d : List Nat := [\n%s]' %
              (c, ',\n'.join('  nat_lit 0x%x' % x for x in tpack(table))), '']
    args = '%d %d %d %d raw Ps' % (OFF, W, M, FLAG)
    for c in range(nseg):
        if c < nseg - 1:
            L += ['theorem ok%d : Snake9.LratV3.check %s t%d %d = true := by' % (c, args, c, c), '  decide +kernel', '']
        else:
            L += ['theorem ok%d : Snake9.LratV3.andB (Snake9.LratV3.check %s t%d %d) (Snake9.LratV3.hasEmpty %d %d (Snake9.LratV3.segP Ps %d)) = true := by'
                  % (c, args, c, c, W, M, c), '  decide +kernel', '']
    L += ['theorem unsat : Unsat cnf := by', '  apply Snake9.LratV3.unsat_of_raw', '  intro τ h',
          '  have hoff : 0 < %d := by decide' % OFF,
          '  have hr : Snake9.LratV3.RawTrue %d τ raw := Snake9.LratV3.rawTrue_of_cnf hoff h' % OFF,
          '  have h0 : Snake9.LratV3.SegsTrue %d %d %d τ Ps 0 := Snake9.LratV3.segsTrue_zero _ _ _ τ Ps' % (OFF, W, M)]
    st = 'Snake9.LratV3.SegsTrue %d %d %d τ Ps' % (OFF, W, M)
    if nseg - 1 <= MAIN_CHUNK:
        for c in range(nseg - 1):
            L.append('  have h%d : %s %d := Snake9.LratV3.seg_step hoff hr ok%d h%d' % (c + 1, st, c + 1, c, c))
    else:
        # long chains of `have`s overflow the elaborator's stack: runs of MAIN_CHUNK steps as lemmas
        thm = L.index('theorem unsat : Unsat cnf := by')
        lem = []
        for a in range(0, nseg - 1, MAIN_CHUNK):
            b = min(a + MAIN_CHUNK, nseg - 1)
            lem += ['theorem steps%d (τ : Nat → Bool) (hoff : 0 < %d) (hr : Snake9.LratV3.RawTrue %d τ raw) (h%d : %s %d) : %s %d := by'
                    % (a, OFF, OFF, a, st, a, st, b)]
            lem += ['  have h%d : %s %d := Snake9.LratV3.seg_step hoff hr ok%d h%d' % (c + 1, st, c + 1, c, c) for c in range(a, b)]
            lem += ['  exact h%d' % b, '']
            L.append('  have h%d : %s %d := steps%d τ hoff hr h%d' % (b, st, b, a, a))
        L[thm:thm] = lem
    L += ['  exact Snake9.LratV3.final_false hoff hr ok%d h%d' % (nseg - 1, nseg - 1), '', 'end ' + ns, '']
    os.makedirs(os.path.join(outroot, 'LocalWindowUnsat'), exist_ok=True)
    p = os.path.join(outroot, 'LocalWindowUnsat', mod + '.lean')
    txt = '\n'.join(L)
    open(p, 'w').write(txt)
    stats['lean_bytes'] = len(txt)
    return stats


def simulate(core_cls, proofs, tables, OFF, W):
    M, FLAG = (1 << W) - 1, 1 << (W - 1)
    taut = 1 | (1 << OFF)

    def bitc(l):
        v = abs(l)
        return taut if v >= OFF else (1 << v if l > 0 else 1 << (v + OFF))
    raw = []
    for cl in core_cls:
        m = 0
        for l in cl:
            m |= bitc(l)
        raw.append(m)

    def lits(x):
        c, n = 0, x & M
        x >>= W
        for _ in range(n):
            c |= 1 << (x & M)
            x >>= W
        return c, x
    lem = [[lits(x)[0] for x in ws] for ws in proofs]

    def resolve(r, cseg):
        s, j = r & 4095, r >> 12
        if s == 0:
            return raw[j] if j < len(raw) else taut
        if s <= cseg:
            return lem[s - 1][j] if j < len(lem[s - 1]) else taut
        return taut
    for c, ws in enumerate(proofs):
        T = tables[c]
        for i, x in enumerate(ws):
            z, h = lits(x)
            n = 0
            ok = False
            while True:
                n += 1
                assert n < HINT_FUEL
                w = h & M
                h >>= W
                if w >= FLAG:
                    e = w - FLAG
                    d = resolve(T[e], c) if 1 <= e < len(T) else taut
                elif w == 0 or w > i:
                    break
                else:
                    d = lem[c][w - 1]
                u = d & ~z
                if u == 0:
                    ok = True
                    break
                if u & (u - 1) == 0:
                    z |= (u >> OFF) if u >= (1 << OFF) else (u << OFF)
            assert ok, ('rup failed', c, i)
    assert any(m == 0 for m in lem[-1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', required=True)
    ap.add_argument('--data', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--seg', type=int, default=60000, help='hints per kernel check (one declaration)')
    ap.add_argument('--off', type=int, default=4000, help='literal offset, above the variable count')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--max-lemmas', type=int, default=4000, help='lemmas per segment at most')
    ap.add_argument('--pack-chunk', type=int, default=16384, help='bytes per ProofPack chunk (at most 16384)')
    ap.add_argument('names', nargs='+')
    a = ap.parse_args()
    for n in a.names:
        print(json.dumps(export(n, a.work, a.data, a.out, a.seg, a.off, a.check, a.pack_chunk,
                                max_lemmas=a.max_lemmas)), flush=True)


if __name__ == '__main__':
    main()
