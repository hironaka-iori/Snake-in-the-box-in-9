"""Write the core and the clause soundness of a window certificate as one packed module.

The k6 certificates have two modules per window: `LocalWindowCnf/<M>.lean` (the UNSAT core
`raw` as a list literal, written by `gen_lean_core.py`) and `LocalWindowSat/<M>.lean` (meaning
tree, counters, tags and the theorem `sat`, written by `gen_lean_sat.py`).  Together they cost
about 0.86 MB of `.olean` per K-sized core, almost all of it the list literals of `raw` (about
75 bytes per literal) and of the counters (about 190 bytes per literal).  This script writes
one module `LocalWindowCnf/<M>.lean` with the same names (`window`, `bounds`, `raw`, `cnf`,
`meaning`, `ctrs`, `tags`, `check`, `sat`), the data packed into `Nat` literals decoded in the
kernel by `work/final_lean/LocalWindowCnfPack.lean`:

* `raw`: `CnfPack.unpackL 8 W [...]`, chunks of at most --chunk bytes, W bits per literal code;
* `ctrs`: `CnfPack.ctrsOf (CnfPack.unpackL 16 W [...])`; a counter that no core clause uses is
  replaced by `[0, 2]` (`⟨[], 2, .ends⟩`, which `ctrOK` accepts and no clause refers to);
* `meaning`: `CnfPack.mtS`, a sparse meaning tree: only the variables of the core clauses and of
  the kept counters get their meaning, every other subtree is `.z` (one bit);
* `tags`: `CnfPack.tagsCL`, 4 bits per tag plus its arguments at the widths of this window.

Widened bounds (milestones/25-k7-234/certify, seeds of `gen_k7_core.py run --plan`): a core JSON
with `lean_bounds` gets `bounds := [(lo, hi), ...]` (those bounds) instead of `boundsOf syms`.  The
CNF and the core are those of the key's own bounds `meta['bounds']`; only the counters that a core
clause uses are kept, and each of them must agree with `lean_bounds` (checked here as `ctrOK`
does in the kernel: an `alpha <= hi` counter needs the same `hi`, an `alpha >= lo` counter the
same `lo`), so `sat` holds for `Axioms` with the wider bounds and the same replay refutes them.

Soundness does not depend on the encoding: `Tags.sound` holds for every meaning tree, counter
and tag list that `checkAll` accepts, and `sat` and the replay's `unsat` are both about
`cnf = raw.map (·.map decodeLit)`.  The script still checks every encoding against a Python
mirror of its decoder, and the core against the CNF (regenerated, `certs/NAME.cnf.gz`) and the
encoding, as `gen_lean_sat.process` does; with --compare it also checks that the core equals
the `raw` of the existing `work/final_lean/LocalWindowCnf/<M>.lean`.

The replay modules import `LocalWindowCnf.<M>` as before; an aggregate imports
`LocalWindowCnf.<M>` instead of `LocalWindowSat.<M>` for `<M>.sat`.

  python gen_lean_cnfsat_packed.py --certs DIR --core DIR --out ROOT [--split] [--compare] [--part-lits N] NAME ...

--split writes the two modules of the old layout instead (`LocalWindowCnf/<M>.lean` with the
packed core, `LocalWindowSat/<M>.lean` with the packed soundness data), for comparison.

--part-lits N (a new path for the H9 windows of milestones/25-k7-234; without it the output is
unchanged) proves `check` in several kernel evaluations, each its own declaration with its own
kernel caches (`work/final_lean/LocalWindowTagsSplit.lean`): `check_ctrs` checks the counters by
`ctrOKL` (the endpoint order on adjacent entries, linear instead of quadratic), and `check_<i>`
the core clauses in consecutive parts of at most N literals (`raw = raw_0 ++ (raw_1 ++ …)`,
`tags` likewise); `checkAll_of_parts` and `ckAll_append` give `check`.  The names and the
statements of `raw`, `cnf`, `tags`, `check` and `sat` are those of the default layout.

--sat-v2 (a new path, milestones/26-replay-efficiency/README.md, "Sat v2"; without it the output is
unchanged) proves the clause soundness with the checker family `TagsW` of
`work/final_lean/LocalWindowTagsW.lean` instead of `Tags.checkAll`: `meaning : Nat → MT` is a flat
table (`mtab`, one field per variable, `TagsW.getF`), the counter literals are a second table
(`ctab`, `TagsW.ctrTab`), and `check : TagsW.checkAllT meaning ctl ctrs window bounds tags raw = true`
is the kernel-native checker (`TagsW.soundT`).  `raw`, `cnf`, `ctrs`, `tags` and the statement of
`sat` are unchanged, so the replays and `Tags.refuted_of_sat` are too.  With --part-lits the parts
are `check_agree` (the counter table), `check_ctrs` and `check_<i>` (`TagsW.ckAllT`).
"""
import argparse, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_lean_sat as GS   # noqa: E402
import wincert              # noqa: E402

ME = 'milestones/10-window-aggregate/scripts/gen_lean_cnfsat_packed.py'


def bl(x):
    return max(1, x.bit_length())


def mask(w):
    return (1 << w) - 1


# ------------------------------------------------------------------ lists ---

def pack_lists(ls, lw, w, cbytes):
    """Chunks `n + 2^16 st` of `CnfPack.unpackL lw w`."""
    groups, cur, bits = [], [], 0
    for l in ls:
        assert len(l) < 1 << lw and all(0 <= x < 1 << w for x in l), (len(l), lw, w)
        b = lw + w * len(l)
        if cur and (bits + b > 8 * cbytes or len(cur) >= 65535):
            groups.append(cur)
            cur, bits = [], 0
        cur.append(l)
        bits += b
    if cur:
        groups.append(cur)
    out = []
    for g in groups:
        st, pos = 0, 0
        for l in g:
            st |= len(l) << pos
            pos += lw
            for x in l:
                st |= x << pos
                pos += w
        out.append(len(g) | (st << 16))
    return out


def unpack_lists(cs, lw, w):
    out = []
    for c in cs:
        n, st = c & 65535, c >> 16
        for _ in range(n):
            k, st = st & mask(lw), st >> lw
            out.append([(st >> (w * i)) & mask(w) for i in range(k)])
            st >>= w * k
    return out


def kind_code(kind):
    return 0 if kind[0] == 'ends' else (1 if kind[0] == 'hi' else 2) + 2 * kind[1]


# ---------------------------------------------------------- meaning tree ---

def leaf_code(m, vw, cw, iw, jw):
    """(code, bits) of `CnfPack.leafS`."""
    if m is None:
        return 0, 2
    if m[0] in ('p', 'e'):
        assert m[1] < 1 << vw
        return (1 if m[0] == 'p' else 2) | (m[1] << 2), 2 + vw
    c, i, j = m[1], m[2], m[3]
    assert c < 1 << cw and i < 1 << iw and j < 1 << jw, m
    return 3 | (c << 2) | (i << (2 + cw)) | (j << (2 + cw + iw)), 2 + cw + iw + jw


def pack_meaning(meaning, nv, used, vw, cw, iw, jw):
    """The stream of `CnfPack.mtS nv vw cw iw jw _ 0 1`: per node a presence bit, then
    the two subtrees or the leaf code; a subtree without used variables is one 0 bit."""
    st, pos = 0, 0

    def rec(r, s, live):   # live: the used indices x of the subtree (x % s == r)
        nonlocal st, pos
        if not live:
            pos += 1
            return
        st |= 1 << pos
        pos += 1
        if r + s <= nv:
            rec(r, 2 * s, [x for x in live if x % (2 * s) == r])
            rec(r + s, 2 * s, [x for x in live if x % (2 * s) == r + s])
        else:
            assert live == [r], (r, s, live)
            code, b = leaf_code(meaning.get(r), vw, cw, iw, jw)
            st |= code << pos
            pos += b
    rec(0, 1, sorted(x for x in used if 0 <= x <= nv))
    return st, pos


def unpack_meaning(st, nv, vw, cw, iw, jw):
    """Python mirror of `CnfPack.mtS`: {index: meaning} of the non-`.z` leaves."""
    out = {}

    def leaf(x):
        k = x & 3
        if k == 0:
            return None, 2
        if k in (1, 2):
            return ('p' if k == 1 else 'e', (x >> 2) & mask(vw)), 2 + vw
        return ('r', (x >> 2) & mask(cw), (x >> (2 + cw)) & mask(iw), (x >> (2 + cw + iw)) & mask(jw)), \
            2 + cw + iw + jw

    def rec(r, s, st):
        if st & 1 == 0:
            return st >> 1
        st >>= 1
        if r + s <= nv:
            return rec(r + s, 2 * s, rec(r, 2 * s, st))
        m, b = leaf(st)
        if m is not None:
            out[r] = m
        return st >> b
    rec(0, 1, st)
    return out


def pack_table(meaning, used, vw, cw, iw, jw):
    """(`--sat-v2`) The flat meaning table of `TagsW.getF T W cw iw`: entry `x` is the field of
    `W = 2 + max(vw, cw + iw + jw)` bits at bit `x * W`, with the code of `CnfPack.leafS`; unused
    variables are `0` (`.z`)."""
    W = 2 + max(vw, cw + iw + jw)
    T = 0
    for x in used:
        code, _ = leaf_code(meaning.get(x), vw, cw, iw, jw)
        assert code < 1 << W
        T |= code << (x * W)
    return T, W


def unpack_table(T, W, cw, iw, xs):
    """Python mirror of `TagsW.getF`."""
    out = {}
    for x in xs:
        f = (T >> (x * W)) & mask(W)
        k = f & 3
        if k in (1, 2):
            out[x] = ('p' if k == 1 else 'e', f >> 2)
        elif k == 3:
            out[x] = ('r', (f >> 2) & mask(cw), (f >> (2 + cw)) & mask(iw), f >> (2 + cw + iw))
    return out


# ------------------------------------------------------------------ tags ---

TAG_KINDS = GS.TAG_KINDS


def tag_code(t, cw, iw, jw):
    """(code, bits) of `CnfPack.tagC`."""
    k = TAG_KINDS.index(t[0])
    a = t[1:]
    if t[0] == 'lowEnd':
        assert a[0] < 16
        return k | (a[0] << 4), 8
    if t[0] in ('first', 'over'):
        c, i = a
        assert c < 1 << cw and i < 1 << iw, t
        return k | (c << 4) | (i << (4 + cw)), 4 + cw + iw
    if t[0] == 'zero':
        c, j = a
        assert c < 1 << cw and j < 1 << jw, t
        return k | (c << 4) | (j << (4 + cw)), 4 + cw + jw
    if t[0] in ('mono', 'step'):
        c, i, j = a
        assert c < 1 << cw and i < 1 << iw and j < 1 << jw, t
        return k | (c << 4) | (i << (4 + cw)) | (j << (4 + cw + iw)), 4 + cw + iw + jw
    assert not a, t
    return k, 4


def pack_tags(tags, cw, iw, jw, cbytes):
    out, cur, st, pos = [], 0, 0, 0
    for t in tags:
        code, b = tag_code(t, cw, iw, jw)
        if cur and (pos + b > 8 * cbytes or cur >= 65535):
            out.append(cur | (st << 16))
            cur, st, pos = 0, 0, 0
        st |= code << pos
        pos += b
        cur += 1
    if cur:
        out.append(cur | (st << 16))
    return out


def unpack_tags(cs, cw, iw, jw):
    out = []
    for c in cs:
        n, st = c & 65535, c >> 16
        for _ in range(n):
            k = TAG_KINDS[st & 15]
            c_ = (st >> 4) & mask(cw)
            i = (st >> (4 + cw)) & mask(iw)
            if k == 'lowEnd':
                t, b = (k, (st >> 4) & 15), 8
            elif k in ('first', 'over'):
                t, b = (k, c_, i), 4 + cw + iw
            elif k == 'zero':
                t, b = (k, c_, (st >> (4 + cw)) & mask(jw)), 4 + cw + jw
            elif k in ('mono', 'step'):
                t, b = (k, c_, i, (st >> (4 + cw + iw)) & mask(jw)), 4 + cw + iw + jw
            else:
                t, b = (k,), 4
            out.append(t)
            st >>= b
    return out


# ------------------------------------------------------------------ core ---

def core_data(name, certs, core_dir):
    """Core clauses (DIMACS), tags, counters and meanings of certificate `name`, with the
    checks of `gen_lean_sat.process` (encoding, committed CNF, cycle cuts)."""
    meta = json.load(open(os.path.join(core_dir, name + '.json')))
    window, bounds = meta['window'], [tuple(b) for b in meta['bounds']]
    if 'dirs' in meta:
        assert window == wincert.window_from_dirs(meta['dirs']), name
    alpha = [b[0] if b[0] == b[1] else b for b in bounds]
    # H9 keys (milestones/25-k7-234): 8 interior vertices, 7 bounds; the last centre is
    # uncounted (`centresOf` takes `bounds.length` centres), so its alpha is None.  Every
    # other set has one bound per centre and pads nothing.
    alpha += [None] * GS.uncounted_centres(window, bounds)
    radius = meta.get('radius', 3)
    enc = GS.TaggedEncoding(window, alpha, radius=radius)
    ref = wincert.Encoding(window, alpha, radius=radius)
    assert ref.clauses == enc.clauses and ref.nv == enc.nv, name
    nv, committed = GS.read_cnf(os.path.join(certs, name + '.cnf.gz'))
    assert nv == enc.nv, (name, nv, enc.nv)
    npre = len(enc.clauses)
    assert committed[:npre] == enc.clauses, name
    inv = {i: v for v, i in enc.var.items()}
    for c in committed[npre:]:
        assert all(l < 0 and -l in inv for l in c), name
        assert GS.is_cycle_set([inv[-l] for l in c]), name
    assert meta['cnf_clauses'] == len(committed), name
    ids = meta['core_ids']
    core = [committed[i - 1] for i in ids]
    tags = [enc.tags[i - 1] if i <= npre else ('cut',) for i in ids]
    return meta, enc, core, tags


def clause_parts(core, part_lits):
    """Consecutive (start, end) ranges of the core with at most `part_lits` literals each (a
    longer clause is a part by itself)."""
    parts, s, acc = [], 0, 0
    for i, c in enumerate(core):
        if i > s and acc + len(c) > part_lits:
            parts.append((s, i))
            s, acc = i, 0
        acc += len(c)
    parts.append((s, len(core)))
    return parts


def emit(name, certs, core_dir, out, chunk=4096, split=False, compare=False, part_lits=0, sat_v2=False):
    meta, enc, core, tags = core_data(name, certs, core_dir)
    module = meta['module'].split('.', 1)[1]
    raw = [[GS.code(l) for l in c] for c in core]
    if compare:
        assert GS.read_lean_raw(module) == raw, name
    # counters: keep those that a core clause refers to
    used_c = {t[1] for t in tags if t[0] in ('first', 'zero', 'mono', 'step', 'over')}
    ctr_lists = [[kind_code(kind), k] + [GS.code(l) for l in lits] if ci in used_c else [0, 2]
                 for ci, (lits, k, kind) in enumerate(enc.ctrs)]
    lean_bounds = meta.get('lean_bounds')
    if lean_bounds is not None:   # widened seed bounds: every kept counter must match them
        lb = [tuple(x) for x in lean_bounds]
        for ci in used_c:
            lits_, k_, kind_ = enc.ctrs[ci]
            if kind_[0] == 'hi':
                assert kind_[1] < len(lb) and lb[kind_[1]][1] == k_, (name, kind_, lb)
            elif kind_[0] == 'lo':
                assert kind_[1] < len(lb) and lb[kind_[1]][0] + k_ == 21, (name, kind_, lb)
        bounds_txt = '[' + ', '.join('(%d, %d)' % x for x in lb) + ']'
    else:
        bounds_txt = 'boundsOf %s' % meta['syms']
    w = bl(max(x for l in raw + ctr_lists for x in l))
    assert max(len(c) for c in raw) < 256
    raw_cs = pack_lists(raw, 8, w, chunk)
    assert unpack_lists(raw_cs, 8, w) == raw
    ctr_cs = pack_lists(ctr_lists, 16, w, chunk)
    assert unpack_lists(ctr_cs, 16, w) == ctr_lists
    # meanings: variables of the core clauses and of the kept counters
    used = {abs(l) for c in core for l in c} | {x // 2 for l in ctr_lists for x in l[2:]}
    ms = [enc.meaning[x] for x in used]
    vw = bl(max([m[1] for m in ms if m[0] in ('p', 'e')] + [0]))
    rs = [m[1:] for m in ms if m[0] == 'r'] + [t[1:] for t in tags if t[0] in ('first', 'zero', 'mono', 'step', 'over')]
    cw = bl(max([r[0] for r in rs] + [0]))
    iw = bl(max([r[1] for r in rs if len(r) == 3] + [t[2] for t in tags if t[0] in ('first', 'over', 'mono', 'step')] + [0]))
    jw = bl(max([r[2] for r in rs if len(r) == 3] + [t[2] for t in tags if t[0] == 'zero'] +
                [t[3] for t in tags if t[0] in ('mono', 'step')] + [0]))
    mst, mbits = pack_meaning(enc.meaning, enc.nv, used, vw, cw, iw, jw)
    assert unpack_meaning(mst, enc.nv, vw, cw, iw, jw) == {x: enc.meaning[x] for x in used}
    tag_cs = pack_tags(tags, cw, iw, jw, chunk)
    assert unpack_tags(tag_cs, cw, iw, jw) == [tuple(t) for t in tags]
    if sat_v2:
        mtab, mw = pack_table(enc.meaning, used, vw, cw, iw, jw)
        assert unpack_table(mtab, mw, cw, iw, range(enc.nv + 1)) == {x: tuple(enc.meaning[x]) for x in used}
        # the counter literals (`TagsW.ctrTab ctab w coffs`): counter c at fields coffs[c] ...
        ctab, coffs, pos = 0, [], 0
        for l in ctr_lists:
            coffs.append(pos)
            for x in l[2:]:
                ctab |= x << (pos * w)
                pos += 1
        assert all((ctab >> ((coffs[c] + i) * w)) & mask(w) == x
                   for c, l in enumerate(ctr_lists) for i, x in enumerate(l[2:]))

    def lits(cs):
        return '[\n' + ',\n'.join('  nat_lit 0x%x' % c for c in cs) + ']'
    dirs, syms = meta['dirs'], meta['syms']
    radius = meta.get('radius', 3)
    head = ('/-! UNSAT core of radius-%d direction certificate `%s` (generated by\n`%s`): %d of\n'
            'the %d clauses of the CNF (regenerated from\n`milestones/10-window-aggregate/data/%s/%s.json`), '
            'in their original order, with the\noriginal variable numbers.  Directions `%s`, lumped counts `%s`.'
            % (radius, name, ME, len(core), meta['cnf_clauses'], os.path.basename(os.path.normpath(core_dir)),
               name, dirs, syms))
    if lean_bounds is not None:
        head += ('\nThe core uses no counter of a widened side, so `bounds` are the widened bounds `%s`\n'
                 '(`gen_k7_core.py run --plan`), wider than `boundsOf %s`.' % (bounds_txt, syms))
    cnf_defs = ['noncomputable def window : List Nat := winOf %s' % dirs,
                'noncomputable def bounds : List (Nat × Nat) := %s' % bounds_txt, '',
                '/-- Literals coded by `decodeLit` (`CnfPack.unpackL`, %d bits each). -/' % w,
                'noncomputable def raw : List (List Nat) := CnfPack.unpackL 8 %d %s' % (w, lits(raw_cs)), '',
                'noncomputable def cnf : List (List Int) := raw.map (·.map decodeLit)', '']
    sat_defs = ['/-- Meanings of the variables of the core and of its counters (`CnfPack.mtS`). -/',
                'noncomputable def meaning : MT :=',
                '  (CnfPack.mtS %d %d %d %d %d 64 0 1 (nat_lit 0x%x)).1' % (enc.nv, vw, cw, iw, jw, mst), '',
                '/-- The sequential counters; those that no core clause uses are `⟨[], 2, .ends⟩`. -/',
                'noncomputable def ctrs : List Ctr := CnfPack.ctrsOf (CnfPack.unpackL 16 %d %s)' % (w, lits(ctr_cs)), '',
                'noncomputable def tags : List Tag := CnfPack.tagsCL %d %d %d %s' % (cw, iw, jw, lits(tag_cs)), '',
                'theorem check : checkAll meaning ctrs window bounds tags raw = true := by decide +kernel', '',
                'theorem sat : ∀ S E : Nat → Bool,',
                '    Axioms S E window (centresOf window bounds) → ∃ τ, cnfTrue τ cnf = true :=',
                '  fun S E h => ⟨tau S E meaning ctrs, sound meaning ctrs window bounds tags raw check S E h⟩', '']
    if sat_v2:   # the flat meaning table and the checker family `TagsW` (LocalWindowTagsW)
        sat_defs = ['/-- Meanings of the variables of the core and of its counters: field `x` of %d bits of `mtab`\n'
                    '(`TagsW.getF`; `0` is `.z`). -/' % mw,
                    'noncomputable def mtab : Nat := nat_lit 0x%x' % mtab,
                    'noncomputable def meaning : Nat → MT := TagsW.getF mtab %d %d %d' % (mw, cw, iw) +
                    '\n\n/-- Literal `i` of counter `c`: field `offs[c] + i` of %d bits of `ctab` (`TagsW.ctrTab`,\n'
                    'checked against `ctrs` by `TagsW.agreeC`). -/\n'
                    'noncomputable def ctab : Nat := nat_lit 0x%x\n'
                    'noncomputable def ctl : Nat → Nat → Nat := TagsW.ctrTab ctab %d [%s]'
                    % (w, ctab, w, ', '.join(map(str, coffs))),
                    ''] + sat_defs[4:9] + [
                    'theorem check : TagsW.checkAllT meaning ctl ctrs window bounds tags raw = true := by decide +kernel',
                    '', 'theorem sat : ∀ S E : Nat → Bool,',
                    '    Axioms S E window (centresOf window bounds) → ∃ τ, cnfTrue τ cnf = true :=',
                    '  fun S E h => ⟨TagsW.tau S E meaning ctrs,\n'
                    '    TagsW.soundT meaning ctl ctrs window bounds tags raw check S E h⟩',
                    '']
    opt = ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    imports = ['import LocalWindowDirModel', 'import LocalWindowCnfPack'] + (['import LocalWindowTagsW'] if sat_v2 else [])
    parts = None
    if part_lits:   # `check` in several declarations (LocalWindowTagsSplit); one module only
        assert not split, '--part-lits needs the one-module layout'
        parts = clause_parts(core, part_lits)
        np_ = len(parts)
        raw_ps = [pack_lists(raw[s:e], 8, w, chunk) for s, e in parts]
        tag_ps = [pack_tags(tags[s:e], cw, iw, jw, chunk) for s, e in parts]
        assert sum((unpack_lists(c, 8, w) for c in raw_ps), []) == raw
        assert sum((unpack_tags(c, cw, iw, jw) for c in tag_ps), []) == [tuple(t) for t in tags]
        raw_cs = [c for cs in raw_ps for c in cs]
        tag_cs = [c for cs in tag_ps for c in cs]

        def nm(base, i):
            return base if np_ == 1 else '%s_%d' % (base, i)

        def app(base):   # base_0 ++ (base_1 ++ (… ++ base_k)), the nesting of `check`
            t = nm(base, np_ - 1)
            for i in reversed(range(np_ - 1)):
                t = '%s ++ (%s)' % (nm(base, i), t) if i < np_ - 2 else '%s ++ %s' % (nm(base, i), t)
            return t
        cnf_defs = ['noncomputable def window : List Nat := winOf %s' % dirs,
                    'noncomputable def bounds : List (Nat × Nat) := %s' % bounds_txt, '',
                    '/-- Literals coded by `decodeLit` (`CnfPack.unpackL`, %d bits each)%s. -/'
                    % (w, '' if np_ == 1 else ', in %d parts' % np_)]
        for i, (s, e) in enumerate(parts):
            cnf_defs += ['noncomputable def %s : List (List Nat) := CnfPack.unpackL 8 %d %s'
                         % (nm('raw', i), w, lits(raw_ps[i])), '']
        if np_ > 1:
            cnf_defs += ['noncomputable def raw : List (List Nat) := %s' % app('raw'), '']
        cnf_defs += ['noncomputable def cnf : List (List Int) := raw.map (·.map decodeLit)', '']
        tag_defs = ['noncomputable def %s : List Tag := CnfPack.tagsCL %d %d %d %s'
                    % (nm('tags', i), cw, iw, jw, lits(tag_ps[i])) for i in range(np_)]
        if np_ > 1:
            tag_defs.append('noncomputable def tags : List Tag := %s' % app('tags'))
        pre, K = ('TagsW.', 'T') if sat_v2 else ('', '')
        checks = (['/-- The counter table agrees with the counters (`TagsW.agreeC`). -/',
                   'theorem check_agree : TagsW.agreeC ctl ctrs 0 = true := by decide +kernel', '']
                  if sat_v2 else []) + ['/-- The counters, with the endpoint order checked on adjacent entries (`ctrOKL`). -/',
                  ('theorem check_ctrs : TagsW.allK (TagsW.ctrOKK meaning (centresK window bounds)) ctrs = true := '
                   'by decide +kernel' if sat_v2 else
                   'theorem check_ctrs : ctrs.all (ctrOKL meaning (centresK window bounds)) = true := by '
                   'decide +kernel'), '']
        for i, (s, e) in enumerate(parts):
            checks += ['/-- Core clauses %d to %d (%d literals). -/' % (s + 1, e, sum(map(len, core[s:e]))),
                       'theorem check_%d : %sckAll%s meaning %sctrs window %s %s = true := by decide +kernel'
                       % (i, pre, K, 'ctl ' if sat_v2 else '', nm('tags', i), nm('raw', i)), '']
        term = 'check_%d' % (np_ - 1)
        for i in reversed(range(np_ - 1)):
            term = pre + 'ckAll' + K + '_append meaning %sctrs window %s%s %s _ _ check_%d\n      (%s)' % (
                'ctl ' if sat_v2 else '', 'check_agree ' if sat_v2 else '', nm('tags', i), nm('raw', i), i, term)
        sat_defs = sat_defs[:7] + ['\n\n'.join(tag_defs), ''] + checks + [
            'theorem check : %scheckAll%s meaning %sctrs window bounds tags raw = true :=' % (pre, K, 'ctl ' if sat_v2 else ''),
            '  %scheckAll%s_of_parts %scheck_ctrs\n    (%s)' % (pre, K, 'check_agree ' if sat_v2 else '', term),
            ''] + sat_defs[-4:]
        if not sat_v2:
            imports.append('import LocalWindowTagsSplit')
        # one kernel check at a time: the parts are separate declarations so that their caches
        # are freed in turn
        opt = opt[:2] + ['set_option Elab.async false', '']
    ns = 'Snake9.LocalWindow.' + module
    files = {}
    if parts:
        doc = head + ('\n`sat`: every clause of the core follows from the snake axioms (`Tags.sound`).  `check` is\n'
                      'proved in %d kernel evaluations: the counters (`check_ctrs`, by `ctrOKL`) and the clauses in\n'
                      '%d part(s) of at most %d literals (`check_<i>`), combined by `checkAll_of_parts` and\n'
                      '`ckAll_append` (`LocalWindowTagsSplit`).  The data are packed (`LocalWindowCnfPack`). -/'
                      % (len(parts) + 1, len(parts), part_lits))
        if sat_v2:
            doc = head + ('\n`sat`: every clause of the core follows from the snake axioms (`TagsW.soundT`,\n'
                          '`LocalWindowTagsW`).  `check` is proved in %d kernel evaluations: the counter table\n'
                          '(`check_agree`), the counters (`check_ctrs`) and the clauses in %d part(s) of at most %d\n'
                          'literals (`check_<i>`), combined by `TagsW.checkAllT_of_parts` and `TagsW.ckAllT_append`.\n'
                          'The data are packed (`LocalWindowCnfPack`, `TagsW.getF`, `TagsW.ctrTab`). -/'
                          % (len(parts) + 2, len(parts), part_lits))
        files['LocalWindowCnf'] = '\n'.join(imports + ['', doc, ''] + opt +
                                            ['namespace ' + ns, '', 'open Snake9.LocalWindow.Tags', ''] +
                                            cnf_defs + sat_defs + ['end ' + ns, ''])
    elif split:
        files['LocalWindowCnf'] = '\n'.join(['import LocalWindowDirModel', 'import LocalWindowCnfPack', '',
                                             head + ' -/', ''] + opt + ['namespace ' + ns, ''] + cnf_defs +
                                            ['end ' + ns, ''])
        files['LocalWindowSat'] = '\n'.join(['import LocalWindowCnfPack', 'import ' + meta['module'], '',
                                             '/-! Every clause of the UNSAT core `%s.cnf` follows from the snake axioms '
                                             '(generated by\n`%s --split`). -/' % (meta['module'], ME), ''] + opt +
                                            ['namespace ' + ns, '', 'open Snake9.LocalWindow.Tags', ''] + sat_defs +
                                            ['end ' + ns, ''])
    else:
        doc = head + ('\n`sat`: every clause of the core follows from the snake axioms (`Tags.sound`, one kernel\n'
                      'evaluation of `checkAll`).  The data are packed (`LocalWindowCnfPack`). -/')
        if sat_v2:
            doc = head + ('\n`sat`: every clause of the core follows from the snake axioms (`TagsW.soundT`, one kernel\n'
                          'evaluation of `TagsW.checkAllT`, `LocalWindowTagsW`).  The data are packed\n'
                          '(`LocalWindowCnfPack`, `TagsW.getF`, `TagsW.ctrTab`). -/')
        files['LocalWindowCnf'] = '\n'.join(imports + ['', doc, ''] +
                                            opt + ['namespace ' + ns, '', 'open Snake9.LocalWindow.Tags', ''] +
                                            cnf_defs + sat_defs + ['end ' + ns, ''])
    for d, txt in files.items():
        os.makedirs(os.path.join(out, d), exist_ok=True)
        p = os.path.join(out, d, module + '.lean')
        if not (os.path.exists(p) and open(p).read() == txt):
            open(p, 'w').write(txt)
    return dict(name=name, module=module, core=len(core), lits=sum(map(len, core)), nv=enc.nv, used=len(used),
                ctrs=len(enc.ctrs), ctrs_kept=len(used_c), w=w, vw=vw, cw=cw, iw=iw, jw=jw,
                raw_bytes=sum((c.bit_length() + 7) // 8 for c in raw_cs), meaning_bytes=(mbits + 7) // 8,
                tag_bytes=sum((c.bit_length() + 7) // 8 for c in tag_cs),
                ctr_bytes=sum((c.bit_length() + 7) // 8 for c in ctr_cs), lean_bytes=sum(map(len, files.values())),
                check_parts=len(parts) if parts else 0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--certs', required=True, help='directory with NAME.cnf.gz (e.g. gen_k6_core.regen_cnf)')
    ap.add_argument('--core', required=True, help='core JSON directory (e.g. data/lean_core_direction_k6)')
    ap.add_argument('--out', required=True, help='Lean root that receives LocalWindowCnf/<M>.lean')
    ap.add_argument('--chunk', type=int, default=4096, help='bytes per chunk literal (at most 16384)')
    ap.add_argument('--split', action='store_true', help='two modules (LocalWindowCnf, LocalWindowSat)')
    ap.add_argument('--compare', action='store_true', help='check the core against work/final_lean/LocalWindowCnf')
    ap.add_argument('--part-lits', type=int, default=0,
                    help='check the counters (by ctrOKL) and the clauses in parts of at most this many literals, '
                         'one declaration each (LocalWindowTagsSplit); 0: one `check` (the default)')
    ap.add_argument('--sat-v2', action='store_true',
                    help='clause soundness by the checker family TagsW (LocalWindowTagsW): a flat meaning table')
    ap.add_argument('names', nargs='+')
    a = ap.parse_args()
    assert 0 < a.chunk <= 16384
    for name in a.names:
        print(json.dumps(emit(name, a.certs, a.core, a.out, a.chunk, a.split, a.compare, a.part_lits, a.sat_v2)), flush=True)


if __name__ == '__main__':
    main()
