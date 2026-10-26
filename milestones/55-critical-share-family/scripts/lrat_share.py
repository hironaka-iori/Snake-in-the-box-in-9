"""Emit kernel-checked LRAT refutations of the 22 window cores as Lean modules.

For certificate NAME this reads the LRAT proof NAME.lrat and the full CNF NAME.cnf
(from the vendored drat-trim, see gen_lean_core.py; not committed) together with the
core data milestones/10-window-aggregate/data/lean_core/NAME.json, and writes

  work/final_lean/LocalWindowUnsat/<Module>.lean
      theorem Snake9.LocalWindow.<Module>.unsat : Unsat cnf
  work/final_lean/LocalWindowUnsat/<Module>/Data<k>.lean   proof data, k = 0..n
  work/final_lean/LocalWindowUnsat/<Module>/Check<g>.lean  kernel checks

The checker is work/final_lean/LratCheck.lean.  Encoding:

* every clause (core input or lemma) occupies a slot from its creation to its last use;
  slots are reused, slot s is a node of a heap-shaped binary tree (children 2s, 2s+1)
  and its search key is the in-order position of that node, so that small slots are
  near the root; inputs used most often get the smallest slots;
* a literal v / -v is bit v / v + 2400, written as the word bit+1;
* a lemma is one Nat of 13-bit words  key lit+1 ... lit+1 0 hint-key ... hint-key 0;
* the proof is cut into segments of about --seg hints, each checked by one
  `decide +kernel` (`check start_k proof_k = true`); the database at the start of
  segment k+1 is `replay start_k proof_k`, or, every --cp segments, a checkpoint
  (the live clauses, `build`) that the previous segment verifies with `cpOk`;
* the last segment also verifies that the empty clause is in the final database.

With --fast the checker is work/final_lean/LratFast.lean (LratFast14 for 14-bit words):
the database is the perfect tree of height h = nslots.bit_length() whose keys are the
in-order positions 1 .. 2^h - 1 (heap node s at depth d, index i in its level, has key
(2i+1) 2^(h-1-d)), so the initial shape is built by one recursion (`perf`), and a
checkpoint lists the clause words of every node of that tree in pre-order, `0` for a free
slot (`build`, checked by `cpOk`).  With --fast all proof data are written as raw literals
(`nat_lit`): no `OfNat` instance per element, so data modules elaborate about twice as fast,
their .olean files are a third smaller, and the kernel never unfolds a numeral.

  python gen_lean_lrat.py --work DIR [--seg N] [--cp M] [--group G] [--check] [--data DIR] NAME ...
"""
import argparse, collections, heapq, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
DATA = os.path.join(HERE, '..', 'data', 'lean_core')
LEAN = os.path.join(ROOT, 'work', 'final_lean')

W = 13
M = (1 << W) - 1
CHECKER_IMPORT, CHECKER_OPEN = 'import LratCheck', 'open Snake9.Lrat'


FAST = False
OFF = 2400
BASE_NS = 'Snake9.Lrat'


def set_width(bits, fast=False, off=2400):
    """Word width of the proof encoding (13, 14 or 15 bits) and literal offset (2400 or
    3000); the checker is LratCheck / LratCheck14 / LratCheckO3k, or with `fast`
    LratFast{,14} / LratFastO3k{,14,15} (see gen_checker_variants.py)."""
    global W, M, CHECKER_IMPORT, CHECKER_OPEN, FAST, OFF, BASE_NS
    assert bits in (13, 14, 15) and off in (2400, 3000, 4000, 5000, 6000, 8000)
    W, M, FAST, OFF = bits, (1 << bits) - 1, fast, off
    osfx = {2400: '', 3000: 'O3k', 4000: 'O4k', 5000: 'O5k', 6000: 'O6k', 8000: 'O8k'}[off]
    wsfx = str(bits) if bits != 13 else ''
    BASE_NS = 'Snake9.Lrat' + osfx
    if fast:
        CHECKER_IMPORT = 'import LratFast' + osfx + wsfx
        CHECKER_OPEN = 'open Snake9.LratFast%s%s\nopen %s (Tree TreeTrue andB)' % (osfx, wsfx, BASE_NS)
    else:
        assert (bits, off) in ((13, 2400), (14, 2400), (13, 3000))
        CHECKER_IMPORT, CHECKER_OPEN = 'import LratCheck' + osfx + wsfx, 'open ' + BASE_NS + wsfx

# Keyword of the proof-data definitions.  The kernel checks only unfold them, so with
# --noncomputable-data they are declared `noncomputable def`: no compiled code is
# generated, which makes the .olean files several times smaller and the .c files empty.
DATA_DEF = 'def'


def module_name(name):
    code, orient, shape = name.split('_')
    return 'C' + code + orient.capitalize() + shape.capitalize()


def read_cnf_core(path, core_ids):
    want = set(core_ids)
    out = {}
    i = 0
    for line in open(path):
        if line.startswith(('p', 'c')) or not line.strip():
            continue
        i += 1
        if i in want:
            lits = [int(x) for x in line.split()]
            assert lits[-1] == 0
            out[i] = lits[:-1]
    return [out[c] for c in core_ids]


def read_lrat(path):
    lemmas = []
    for line in open(path):
        t = line.split()
        if t[1] == 'd':
            continue
        t = [int(x) for x in t]
        z = t.index(0, 1)
        hints = t[z + 1:-1]
        assert t[-1] == 0 and all(h > 0 for h in hints), 'RAT hints are not supported'
        lemmas.append((t[0], t[1:z], hints))
    return lemmas


def plan(core_ids, lemmas):
    """Slots (heap nodes).  Returns input slots, per-lemma (slot, lits, hint slots),
    last use of every clause id, and the number of slots."""
    uses = collections.Counter()
    last = {}
    for i, (cid, lits, hints) in enumerate(lemmas):
        for h in hints:
            uses[h] += 1
            last[h] = i
    final = lemmas[-1][0]
    assert lemmas[-1][1] == [], 'last lemma must be the empty clause'
    last[final] = len(lemmas)
    for c in core_ids:
        last.setdefault(c, -1)   # an unused core clause keeps its slot (loaded, never freed)
    order = sorted(core_ids, key=lambda c: (-uses[c], c))
    slot_of = {c: s for s, c in enumerate(order, start=1)}
    free = []
    nxt = len(order) + 1
    expire = collections.defaultdict(list)
    for c, i in last.items():
        expire[i].append(c)
    steps = []
    for i, (cid, lits, hints) in enumerate(lemmas):
        hs = [slot_of[h] for h in hints]
        for c in expire.get(i, []):
            heapq.heappush(free, slot_of[c])
        if free:
            s = heapq.heappop(free)
        else:
            s = nxt
            nxt += 1
        slot_of[cid] = s
        if cid not in last:
            heapq.heappush(free, s)
        steps.append((s, lits, hs))
    return [slot_of[c] for c in core_ids], steps, last, nxt - 1


def inorder_keys(n):
    key = {}
    cnt = 0
    stack = []
    node = 1
    while stack or node <= n:
        while node <= n:
            stack.append(node)
            node = 2 * node
        node = stack.pop()
        cnt += 1
        key[node] = cnt
        node = 2 * node + 1
    return key


def perfect_keys(n):
    """Keys of heap nodes 1..n in the perfect tree of height h = n.bit_length(): the
    in-order positions, as in `perf h 0` of LratFast."""
    h = n.bit_length()
    key = {}
    for s in range(1, n + 1):
        d = s.bit_length() - 1
        key[s] = (2 * (s - (1 << d)) + 1) << (h - 1 - d)
    return h, key


def preorder_keys(h):
    """Keys of `perf h 0` in pre-order."""
    out = []

    def visit(d, b):
        if d == 0:
            return
        k = b + (1 << (d - 1))
        out.append(k)
        visit(d - 1, b)
        visit(d - 1, k)
    visit(h, 0)
    return out


def bit(l):
    v = abs(l)
    assert 0 < v < OFF
    return v if l > 0 else v + OFF


def pack(ws):
    x = 0
    for j, w in enumerate(ws):
        assert 0 <= w <= M
        x |= w << (W * j)
    return x


def cmask(lits):
    m = 0
    for l in lits:
        m |= 1 << bit(l)
    return m


def unpack(x):
    out = []
    while x:
        out.append(x & M)
        x >>= W
    return out


# ---------------------------------------------------------------- simulator ---

def sim_lits(ws, pos):
    c = 0
    while pos < len(ws) and ws[pos] != 0:
        c |= 1 << (ws[pos] - 1)
        pos += 1
    return c, pos + 1


def sim_rup(db, x):
    ws = unpack(x)
    c, pos = sim_lits(ws, 1)
    z = c
    while True:
        w = ws[pos] if pos < len(ws) else 0
        pos += 1
        if w not in db:
            return False
        d = db[w]
        u = d & ~z
        if u == 0:
            return True
        if u & (u - 1) == 0:
            z |= (u << OFF) if u < (1 << OFF) else (u >> OFF)


def sim_ins(db, x):
    ws = unpack(x)
    c, _ = sim_lits(ws, 1)
    db[x & M] = c


def sim_ent(x):
    c, _ = sim_lits(unpack(x), 1)
    return x & M, c


# ---------------------------------------------------------------- emitter ---

def hexlist(xs):
    if not xs:
        return '[]'
    lit = (lambda x: 'nat_lit ' + (hex(x) if x > 9 else str(x))) if FAST else (lambda x: hex(x) if x > 9 else str(x))
    if len(xs) > 16384:
        # a single literal this long overflows the elaborator's stack: append chunks
        parts = ['[\n  ' + ',\n  '.join(lit(x) for x in xs[i:i + 2048]) + ']' for i in range(0, len(xs), 2048)]
        out = parts[-1]
        for p in reversed(parts[:-1]):
            out = 'List.append ' + p + '\n (' + out + ')'
        return out
    return '[\n  ' + ',\n  '.join(lit(x) for x in xs) + ']'


def declist(xs, per_line=32):
    lit = (lambda x: 'nat_lit %d' % x) if FAST else str
    lines = []
    for i in range(0, len(xs), per_line):
        lines.append(', '.join(lit(x) for x in xs[i:i + per_line]))
    return '[\n  ' + ',\n  '.join(lines) + ']'


HEADER = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'


def export(name, work, seg_hints, cp_every, group, check, outroot, data=DATA):
    meta = json.load(open(os.path.join(data, name + '.json')))
    mod = meta['module'].split('.')[-1] if 'module' in meta else module_name(name)
    core_ids = meta['core_ids']
    core_cls = read_cnf_core(os.path.join(work, name + '.cnf'), core_ids)
    lemmas = read_lrat(os.path.join(work, name + '.lrat'))
    input_slots, steps, last, nslots = plan(core_ids, lemmas)
    assert nslots <= M
    if FAST:
        height, key = perfect_keys(nslots)
    else:
        key = inorder_keys(nslots)
    nums = [pack([key[s]] + [bit(l) + 1 for l in lits] + [0] + [key[h] for h in hs] + [0])
            for s, lits, hs in steps]
    # segments
    cuts = [0]
    acc = 0
    for i, (_, _, hs) in enumerate(steps):
        acc += len(hs)
        if acc >= seg_hints and i + 1 < len(steps):
            cuts.append(i + 1)
            acc = 0
    cuts.append(len(steps))
    nseg = len(cuts) - 1
    lits_of, born, slot_at = {}, {}, {}
    for c, cl, s in zip(core_ids, core_cls, input_slots):
        lits_of[c], born[c], slot_at[c] = cl, -1, s
    for i, ((cid, lits, _), (s, _, _)) in enumerate(zip(lemmas, steps)):
        lits_of[cid], born[cid], slot_at[cid] = lits, i, s
    is_cp = [False] * (nseg + 2)   # is_cp[k]: segment k starts from a checkpoint
    cps = {}
    for k in range(2, nseg + 1):
        if (k - 1) % cp_every == 0:
            is_cp[k] = True
            j = cuts[k - 1]
            live = sorted((slot_at[c], c) for c, l in last.items() if born[c] < j and l >= j)
            if FAST:
                by_key = {key[s]: pack([bit(l) + 1 for l in lits_of[c]]) for s, c in live}
                assert all(by_key.values())
                cps[k] = [by_key.get(kk, 0) for kk in preorder_keys(height)]
            else:
                cps[k] = [pack([key[s]] + [bit(l) + 1 for l in lits_of[c]]) for s, c in live]
    final_key = key[steps[-1][0]]
    stats = dict(name=name, module=mod, lemmas=len(steps), hints=sum(len(h) for _, _, h in steps),
                 slots=nslots, segments=nseg, checkpoints=len(cps),
                 seg_hints=[sum(len(h) for _, _, h in steps[cuts[k]:cuts[k + 1]]) for k in range(nseg)])
    if check:
        taut = 1 | (1 << OFF)
        db = {key[s]: taut for s in range(1, nslots + 1)}
        if FAST:
            db = {kk: taut for kk in range(1, 1 << height)}
        for s, cl in zip(input_slots, core_cls):
            db[key[s]] = cmask(cl)
        for k in range(1, nseg + 1):
            if is_cp[k] and FAST:
                ndb = {}
                for kk, e in zip(preorder_keys(height), cps[k]):
                    c = taut if e == 0 else sim_lits(unpack(e), 0)[0]
                    assert c == taut or db.get(kk) == c, ('checkpoint', k, kk)
                    ndb[kk] = c
                db = ndb
            elif is_cp[k]:
                ndb = {key[s]: taut for s in range(1, nslots + 1)}
                for e in cps[k]:
                    kk, c = sim_ent(e)
                    assert db.get(kk) == c, ('checkpoint', k, kk)
                    ndb[kk] = c
                db = ndb
            for x in nums[cuts[k - 1]:cuts[k]]:
                assert sim_rup(db, x), ('rup failed', k)
                sim_ins(db, x)
        assert db.get(final_key) == 0
        stats['simulated'] = True
    # ---- write Lean
    outdir = os.path.join(outroot, 'LocalWindowUnsat')
    sub = os.path.join(outdir, mod)
    os.makedirs(sub, exist_ok=True)
    ns = 'Snake9.LocalWindow.' + mod
    files = {}
    files[os.path.join(sub, 'Data0.lean')] = '\n'.join([
        CHECKER_IMPORT, 'import LocalWindowCnf.' + mod, '',
        '/-! LRAT refutation of the core of `%s`: database shape and input slots' % name,
        '(generated by `milestones/10-window-aggregate/scripts/gen_lean_lrat.py`). -/', '',
        HEADER, 'namespace ' + ns, CHECKER_OPEN, '',
        *([] if FAST else [
            '/-- Keys of the database nodes in breadth-first order. -/',
            DATA_DEF + ' shapeKeys : List Nat := ' + declist([key[s] for s in range(1, nslots + 1)]),
            '']),
        '/-- Key of each core clause. -/',
        DATA_DEF + ' inputSlots : List Nat := ' + declist([key[s] for s in input_slots]), '',
        ('noncomputable def start1 : Tree := loadRaw (perf %d 0) raw inputSlots' % height if FAST
         else 'noncomputable def start1 : Tree := loadRaw (shape .nil shapeKeys) raw inputSlots'), '',
        'end ' + ns, ''])
    for k in range(1, nseg + 1):
        # Data_k needs start_k (from Data_{k-1}) only to define start_{k+1} as a replay; at a
        # checkpoint, and for the last segment, it imports Data0 alone, so that import chains
        # have at most --cp links instead of growing with the segment index.
        needs_prev = k < nseg and not is_cp[k + 1]
        body = ['import LocalWindowUnsat.%s.Data%d' % (mod, k - 1 if needs_prev else 0), '',
                '/-! LRAT refutation of the core of `%s`: segment %d of %d (generated). -/' % (name, k, nseg), '',
                HEADER, 'namespace ' + ns, CHECKER_OPEN, '',
                DATA_DEF + ' proof%d : List Nat := %s' % (k, hexlist(nums[cuts[k - 1]:cuts[k]])), '']
        if k < nseg:
            if is_cp[k + 1]:
                body += ['/-- Checkpoint: the live clauses before segment %d. -/' % (k + 1),
                         DATA_DEF + ' cp%d : List Nat := %s' % (k + 1, hexlist(cps[k + 1])), '',
                         ('noncomputable def start%d : Tree := build %d cp%d' % (k + 1, height, k + 1) if FAST
                          else 'noncomputable def start%d : Tree := build (shape .nil shapeKeys) cp%d'
                          % (k + 1, k + 1)), '']
            else:
                body += ['noncomputable def start%d : Tree := replay start%d proof%d' % (k + 1, k, k), '']
        body += ['end ' + ns, '']
        files[os.path.join(sub, 'Data%d.lean' % k)] = '\n'.join(body)

    def seg_prop(k):
        base = 'check start%d proof%d' % (k, k)
        if k == nseg:
            return 'andB (%s) (hasEmpty (replay start%d proof%d) %d) = true' % (base, k, k, final_key)
        if is_cp[k + 1] and FAST:
            return 'andB (%s) (cpOk (replay start%d proof%d) start%d) = true' % (base, k, k, k + 1)
        if is_cp[k + 1]:
            return 'andB (%s) (cpOk (replay start%d proof%d) cp%d) = true' % (base, k, k, k + 1)
        return '%s = true' % base

    groups = [list(range(g, min(g + group, nseg + 1))) for g in range(1, nseg + 1, group)]
    for gi, ks in enumerate(groups, start=1):
        # start_k lives in Data_{k-1}, proof_k in Data_k: import the whole range explicitly
        body = ['import LocalWindowUnsat.%s.Data%d' % (mod, j) for j in range(ks[0] - 1, ks[-1] + 1)] + ['',
                '/-! Kernel checks of segments %d-%d of `%s` (generated). -/' % (ks[0], ks[-1], name), '',
                HEADER, 'set_option Elab.async false', '', 'namespace ' + ns, CHECKER_OPEN, '']
        for k in ks:
            body += ['theorem ok%d : %s := by' % (k, seg_prop(k)), '  decide +kernel', '']
        body += ['end ' + ns, '']
        files[os.path.join(sub, 'Check%d.lean' % gi)] = '\n'.join(body)
    main = ['import LocalWindowUnsat.%s.Check%d' % (mod, gi) for gi in range(1, len(groups) + 1)]
    main += ['', '/-! Kernel-checked LRAT refutation of the core of `%s`: %d lemmas, %d hints,' % (name, stats['lemmas'], stats['hints']),
             '%d segments (generated by `milestones/10-window-aggregate/scripts/gen_lean_lrat.py`). -/' % nseg, '',
             'namespace ' + ns, CHECKER_OPEN, *(['open %s (unsat_of_raw)' % BASE_NS] if FAST else []), '',
             'theorem unsat : Unsat cnf := by',
             '  apply unsat_of_raw',
             '  intro τ h',
             '  have h1 : TreeTrue τ start1 :=',
             ('    start_true (raw := raw) (h := %d) (slots := inputSlots) τ h' % height if FAST else
              '    start_true (raw := raw) (keys := shapeKeys) (slots := inputSlots) τ h')]
    for k in range(1, nseg + 1):
        if k == nseg:
            main.append('  exact final_false (s := start%d) (ps := proof%d) τ ok%d h%d' % (k, k, k, k))
        elif is_cp[k + 1]:
            main.append('  have h%d : TreeTrue τ start%d :=' % (k + 1, k + 1))
            if FAST:
                main.append('    cp_true (s := start%d) (ps := proof%d) (t := start%d) τ ok%d h%d'
                            % (k, k, k + 1, k, k))
            else:
                main.append('    cp_true (s := start%d) (ps := proof%d) (cp := cp%d) (keys := shapeKeys) τ ok%d h%d'
                            % (k, k, k + 1, k, k))
        else:
            main.append('  have h%d : TreeTrue τ start%d :=' % (k + 1, k + 1))
            main.append('    replay_true (t := start%d) (ps := proof%d) τ ok%d h%d' % (k, k, k, k))
    main += ['', 'end ' + ns, '']
    files[os.path.join(outdir, mod + '.lean')] = '\n'.join(main)
    total = 0
    for p, txt in files.items():
        with open(p, 'w') as f:
            f.write(txt)
        total += len(txt)
    stats['lean_bytes'] = total
    stats['check_modules'] = len(groups)
    return stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', required=True, help='directory with NAME.lrat and NAME.cnf')
    ap.add_argument('--seg', type=int, default=30000, help='hints per kernel check')
    ap.add_argument('--cp', type=int, default=4, help='checkpoint every CP segments')
    ap.add_argument('--group', type=int, default=6, help='segments per check module')
    ap.add_argument('--out', default=LEAN)
    ap.add_argument('--check', action='store_true', help='simulate the checker first')
    ap.add_argument('--data', default=DATA, help='core JSON directory (lean_core_direction for the 239 set)')
    ap.add_argument('--wbits', type=int, default=13, help='13, 14 or 15: more than 8191 / 16383 live clauses')
    ap.add_argument('--off', type=int, default=2400, help='literal offset: 2400, 3000 or 4000 (above the variable count)')
    ap.add_argument('--noncomputable-data', action='store_true',
                    help='declare the proof data `noncomputable def` (smaller build output)')
    ap.add_argument('--fast', action='store_true', help='emit proofs for LratFast (see above)')
    ap.add_argument('names', nargs='+')
    a = ap.parse_args()
    set_width(a.wbits, a.fast, a.off)
    if a.noncomputable_data:
        global DATA_DEF
        DATA_DEF = 'noncomputable def'
    for name in a.names:
        print(json.dumps(export(name, a.work, a.seg, a.cp, a.group, a.check, a.out, a.data)), flush=True)


if __name__ == '__main__':
    main()
