"""Context share certificates (ctx 7 / ctx 8) for the Lean framework of milestone 35.

  nice -n 10 python3 ctxcert.py --out DIR CTX DIRS T CAP [CTX DIRS T CAP ...]
  e.g.  ctxcert.py --out ../lean 7 0123412 236664 15   8 01234032 544643 15

Per key (ctx, dirs, t, cap) this writes two Lean modules under DIR:

* `LocalWindowCtxCnf/<N>.lean`: the UNSAT core of the context share CNF, its meanings and tags, and
  `sat : ∀ S E, Axioms S E window (centresOf window bounds) →
          shareSum 12 S ((centresOf window bounds).drop k) ≤ cap → ∃ τ, cnfTrue τ cnf = true`
  by `TagsSW.soundSC` (`work/final_lean/LocalWindowShareCtx.lean`);
* `LocalWindowCtxUnsat/<N>.lean`: the checker-v3 replay of a CaDiCaL LRAT refutation of that core
  (`unsat : Unsat cnf`, `milestones/26-replay-efficiency/scripts/gen_lean_lrat_v3.py`).

`N = C<ctx><dirs>A<t>K<cap>`.  Semantics (milestones/28-combined-identities/share7.py): the window
is `winOf dirs` (7 or 8 directions), the bounds are `boundsOf t` (ctx 7) or `(1, 21) :: boundsOf t`
(ctx 8, the count at the first centre free), the share cap is on the centres from index
`k = len(bounds) - 5` on (the trailing five).  The CNF is `share233.TaggedShare` with the share
part (empty squares, totalizers, thresholds, cap totalizer) built over the trailing five centres
only, i.e. `share7.SubShareEncoding` up to the variable numbering.  `RefutedShareFrom (winOf dirs)
bounds 12 cap k` follows by `TagsSW.refutedShareFrom_of_sat sat unsat`.

The Lean source of the `LocalWindowCnf` module is produced by `cert233.emit_share` (monkeypatched
encoding) and rewritten in its five context-specific lines; the rewrite is asserted.
"""
import argparse, collections, itertools, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '33-233-lean', 'certify'))
import cert233 as C                 # noqa: E402
import share233                     # noqa: E402
GC, K, wincert = C.GC, C.K, C.wincert
FREE = (1, 21)


class TaggedShareCtx(share233.TaggedShare):
    """`TaggedShare` whose share part covers only the centres with 0-based index >= k."""

    def __init__(self, dirs, bounds, cap, k, M=12):
        self.window = wincert.window_from_dirs(list(dirs)); self.bounds = [tuple(b) for b in bounds]
        self.cap = cap; self.M = M; self.k = k
        alpha = [b[0] if b[0] == b[1] else tuple(b) for b in self.bounds]
        base = share233.TaggedEncoding(self.window, alpha, radius=4)
        self.nv = base.nv; self.meaning = base.meaning; self.smeaning = {}; self.ctrs = base.ctrs
        self.clauses = base.clauses; self.tags = [('old', t) for t in base.tags]; self.var = base.var
        self.ball = base.ball
        self.tots = []; spec = []; ulits = []
        for ci, c in enumerate(self.window[1:-1], 1):
            if ci - 1 < k:
                continue
            used = {(c ^ self.window[ci - 1]).bit_length() - 1, (c ^ self.window[ci + 1]).bit_length() - 1}
            cs = []
            for kk in range(9):
                if kk in used:
                    continue
                q = c ^ (1 << kk); es = []
                for a, b in itertools.combinations(range(9), 2):
                    if kk in (a, b):
                        continue
                    e = self.fresh(('sq', q, a, b)); es.append(e)
                    self.add([self.var[v] for v in (q, q ^ (1 << a), q ^ (1 << b), q ^ (1 << a) ^ (1 << b))] + [e],
                             ('emptyE',))
                et, ge = self.totalizer(es, ('emp', q), up=True)
                dt, gd = self.totalizer([self.var[q ^ (1 << a)] for a in range(9)], ('nb', q), up=False, down=True)
                tmax = min(cap + 1, M * len(es)); cs.append((kk, tmax))
                for t in range(1, tmax + 1):
                    u = self.fresh(('u', q, t)); ulits.append(u)
                    for d in range(1, 10):
                        need = (t * d + M - 1) // M
                        if need > len(es):
                            continue
                        clause = [u, -ge[need]]
                        if d < 9:
                            clause.append(gd[d + 1])
                        self.add(clause, ('shareCl', et, dt))
            spec.append(cs)
        ti, out = self.totalizer(ulits, ('cap', spec), up=True, limit=cap + 1)
        self.add([-out[cap + 1]], ('shareCap', ti))
        self.nbase = len(self.clauses)


def bounds_of(ctx, t):
    b = GC.dir_bounds(list(t))
    return ([FREE] + b) if ctx == 8 else b


def name_of(ctx, dirs, t, cap):
    return 'C%d%sA%sK%d' % (ctx, ''.join(map(str, dirs)), ''.join(map(str, t)), cap)


def enc_of(meta, cuts=None):
    enc = TaggedShareCtx(meta['dirs'], meta['bounds'], meta['cap'], meta['k'], M=C.MRES)
    for c in cuts or []:
        enc.add_cut(c)
    return enc


def core(ctx, dirs, t, cap, work, certs, cad, tl):
    name = name_of(ctx, dirs, t, cap)
    bounds = bounds_of(ctx, t)
    assert len(dirs) == ctx and len(bounds) + 1 == ctx and len(t) == 6
    meta = {'name': name, 'module': 'LocalWindowCnf.' + name, 'kind': 'ctxshare', 'ctx': ctx,
            'dirs': list(dirs), 'syms': list(t), 'bounds': [list(b) for b in bounds], 'k': len(bounds) - 5,
            'cap': cap, 'resolution': C.MRES, 'window': wincert.window_from_dirs(list(dirs)), 'radius': 4}
    enc = enc_of(meta)
    npre = len(enc.clauses)
    st, cuts, sec = share233.solve(enc, tl)
    assert st == 'UNSAT', (name, st)
    gz = os.path.join(certs, name + '.cnf.gz')
    sha = C.write_cnf_gz(enc.nv, enc.clauses, gz)
    t1 = time.time()
    cnf = GC.extract_cnf(name, work, certs)
    nl, nh, desc, ids = GC.best_cadical_proof(cnf, os.path.join(work, name + '.full'), cad, [1],
                                              portfolio=[['--unsat']], rounds=1)
    os.remove(os.path.join(work, name + '.full.lrat'))
    for p in (gz, cnf):
        if os.path.exists(p):
            os.remove(p)
    ren, core_, tags, _ = C.share_compact(enc, ids)
    meta.update({'result': 'UNSAT', 'full_variables': enc.nv, 'full_clauses': len(enc.clauses), 'base_clauses': npre,
                 'full_sha256': sha, 'cycle_cuts': cuts, 'full_core_ids': ids, 'variables': len(ren),
                 'cnf_clauses': len(ids), 'core_ids': list(range(1, len(ids) + 1)),
                 'core_kinds': dict(collections.Counter(x[0] if x[0] != 'old' else 'old.' + x[1][0] for x in tags)),
                 'core_producer': f'cadical --lrat {desc} on the full ctx share CNF, trimmed ({nl} lemmas, {nh} hints)',
                 'secs': {'solve': round(sec, 2), 'core': round(time.time() - t1, 2)}})
    return meta


def regen(meta):
    enc = enc_of(meta, meta['cycle_cuts'])
    data = (f'p cnf {enc.nv} {len(enc.clauses)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in enc.clauses)).encode()
    import hashlib
    assert hashlib.sha256(data).hexdigest() == meta['full_sha256'], meta['name']
    return (enc,) + C.share_compact(enc, meta['full_core_ids'])


def emit_cnf(meta, out):
    """cert233.emit_share on the context encoding, then the context-specific rewrite."""
    C.share_regen = regen
    tmp = os.path.join(out, '_tmp')
    r = C.emit_share(meta, tmp)
    name, k = meta['name'], meta['k']
    src = open(os.path.join(tmp, 'LocalWindowCnf', name + '.lean')).read()
    os.remove(os.path.join(tmp, 'LocalWindowCnf', name + '.lean'))
    bl = '[%s]' % ', '.join('(%d, %d)' % tuple(b) for b in meta['bounds'])
    rep = [
        ('import LocalWindowTagsSharePacked', 'import LocalWindowTagsSharePacked\nimport LocalWindowShareCtx'),
        ('noncomputable def bounds : List (Nat × Nat) := boundsOf %s' % meta['syms'],
         'noncomputable def bounds : List (Nat × Nat) := %s\nnoncomputable def first : Nat := %d' % (bl, k)),
        ('tots.all (TagsSW.totOK meaning smeaning window (centresK window bounds))',
         'tots.all (TagsSW.totOK meaning smeaning window ((centresK window bounds).drop first))'),
        ('theorem check : TagsSW.checkAllS meaning smeaning resolution ctrs tots window bounds cap tags raw = true :=\n'
         '  TagsSW.checkAllS_of_parts',
         'theorem check : TagsSW.checkAllSC meaning smeaning resolution ctrs tots window bounds first cap tags raw = true :=\n'
         '  TagsSW.checkAllSC_of_parts'),
        ('    AxiomsS S E window (centresOf window bounds) resolution cap → ∃ τ, cnfTrue τ cnf = true :=\n'
         '  fun S E h => ⟨TagsSW.tauS S E meaning smeaning resolution ctrs tots,\n'
         '    TagsSW.soundS meaning smeaning resolution ctrs tots window bounds cap tags raw check S E h⟩',
         '    Axioms S E window (centresOf window bounds) →\n'
         '      shareSum resolution S ((centresOf window bounds).drop first) ≤ cap → ∃ τ, cnfTrue τ cnf = true :=\n'
         '  fun S E h hc => ⟨TagsSW.tauS S E meaning smeaning resolution ctrs tots,\n'
         '    TagsSW.soundSC meaning smeaning resolution ctrs tots window bounds first cap tags raw check S E h hc⟩'),
    ]
    for a, b in rep:
        assert src.count(a) == 1, a
        src = src.replace(a, b)
    # the header comment: state the context semantics
    src = src.replace('/-! UNSAT core of the share threshold', '/-! Context share threshold (ctx %d, share cap on the '
                      'centres from index %d on; milestones/35-231-lean/scripts/ctxcert.py).\nUNSAT core of the share '
                      'threshold' % (meta['ctx'], k), 1)
    assert 'AxiomsS' not in src and 'boundsOf' not in src.split('namespace', 1)[1]
    d = os.path.join(out, 'LocalWindowCtxCnf')
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, name + '.lean'), 'w').write(src)
    return r


def replay(meta, out, work, certs, cad):
    enc, ren, core_, tags, _ = regen(meta)
    name = meta['name']
    rl = lambda x: (1 if x > 0 else -1) * ren[abs(x)]   # noqa: E731
    gz = os.path.join(certs, name + '.cnf.gz')
    C.write_cnf_gz(len(ren), [[rl(x) for x in c] for c in core_], gz)
    jd = os.path.join(work, 'json')
    C.plain_json(meta, jd)
    _, info = GC.core_lrat(name, meta['core_ids'], work, cad, [1, 2], certs, rounds=2)
    GC.extract_cnf(name, work, certs)
    tmp = os.path.join(out, '_tmp')
    cmd = [sys.executable, C.V3, '--work', work, '--data', jd, '--out', tmp, '--seg', '60000',
           '--off', str(C.offset(meta['variables'])), '--warm', str(C.WARM), name]
    r = subprocess.run(['nice', '-n', '10', *cmd], capture_output=True, text=True)
    assert r.returncode == 0, r.stderr[-3000:]
    p = os.path.join(tmp, 'LocalWindowUnsat', name + '.lean')
    src = open(p).read()
    os.remove(p)
    assert src.count('import LocalWindowCnf.' + name) == 1
    src = src.replace('import LocalWindowCnf.' + name, 'import LocalWindowCtxCnf.' + name)
    d = os.path.join(out, 'LocalWindowCtxUnsat')
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, name + '.lean'), 'w').write(src)
    for x in [os.path.join(work, name + e) for e in ('.lrat', '.lrat.json', '.core.cnf', '.cnf')] + [gz]:
        if os.path.exists(x):
            os.remove(x)
    return {'hints': info['hints'], 'producer': info['producer'], **json.loads(r.stdout.strip().splitlines()[-1])}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--out', required=True, help='root of the generated Lean sources')
    ap.add_argument('--work', default=os.path.join(os.environ.get('CTXCERT_SCR', '/tmp'), 'ctxcert'))
    ap.add_argument('--tl', type=float, default=600)
    ap.add_argument('keys', nargs='+')
    a = ap.parse_args()
    assert len(a.keys) % 4 == 0
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    cad = C.cadical(a.work)
    recs = []
    for i in range(0, len(a.keys), 4):
        ctx, dirs, t, cap = int(a.keys[i]), [int(x) for x in a.keys[i + 1]], [int(x) for x in a.keys[i + 2]], int(a.keys[i + 3])
        t0 = time.time()
        meta = core(ctx, dirs, t, cap, a.work, certs, cad, a.tl)
        r1 = emit_cnf(meta, a.out)
        r2 = replay(meta, a.out, a.work, certs, cad)
        rec = {'name': meta['name'], 'ctx': ctx, 'dirs': dirs, 't': t, 'cap': cap, 'k': meta['k'],
               'bounds': meta['bounds'], 'full_clauses': meta['full_clauses'], 'core': meta['cnf_clauses'],
               'variables': meta['variables'], 'core_kinds': meta['core_kinds'], 'core_producer': meta['core_producer'],
               'cnf_module': r1, 'replay': r2, 'secs': round(time.time() - t0, 1)}
        print(json.dumps(rec), flush=True)
        recs.append(rec)
        json.dump(meta, open(os.path.join(a.out, meta['name'] + '.core.json'), 'w'))


if __name__ == '__main__':
    main()
