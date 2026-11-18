#!/usr/bin/env python3
"""Certificates of the K7 cap-7 route to m <= 230 (milestone 37): window exclusions with arbitrary
count INTERVALS and radius 3 or 4, produced by the unchanged prod435 / cert231 / cert233 plain-key
pipeline through a small adapter.

    c230.py plan [--src milestones/37-230-feasibility/data/k7_uncovered.json.gz] [--out PLAN]
    c230.py cert STEP [cert231 args...]      (what prod435 runs instead of cert435.py; PROD435_CERT)
    c230.py names PLAN [--min-est H]         list the plan's module names (largest first)
    c230.py shareplan [--src SHAPES.jsonl] [--out PLAN]   the 132 corner-share items (share route of prod435)

Statement of every certificate (the public theorem of module `LocalWindowCert.<NAME>`):

    Snake9.LocalWindow.Refuted (winOf-literal window) [(lo0, hi0), (lo1, hi1), ...]

i.e. exactly the 233/231 plain form, with the key's own interval bounds written as a literal list
(`lean_bounds`, the widened-seed path of gen_lean_cnfsat_packed). `Refuted` is radius-free; the
radius only selects the ball of the CNF. It goes through `LocalWindow.refuted_bridge` (core stack,
`LocalWindowBridge`), which takes arbitrary bounds.

Key encoding inside the pipeline (cert231 keys are `(dirs, syms)` with int syms): one code per count,
    1..5 -> (s, s), 6 -> (6, 21)   (unchanged: the 233 meaning of `boundsOf`)
    16 -> (6, 6), 17 -> (7, 7), 18 -> (8, 21)
Module name: 'V' + dirs + 'A' + one character per code (1-5, G = [6,21], 6, 7, H = [8,21]), e.g.
`V01203104A34575H4`; the 'V' prefix never clashes with the S/T/C names of the 233/231 families.

Adapter (apply(), also imported by prod435.py through $PROD435_ADAPTER): decodes the codes in
gen_lean_core.dir_bounds and families_k7.bound_of, names keys as above, sets gen_k7_core.RADIUS from
the plan, writes `lean_bounds` (= the key's bounds) and the true radius into every core JSON, and sets
the replay defaults of SPLIT.md: one round of the 3-configuration portfolio (`--unsat`,
`--unsat --subsume=0`, default), and the low-memory generator genv3stream.py.
"""
import gzip, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
DEFAULT_SRC = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'k7_uncovered.json.gz')
DEFAULT_PLAN = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'c230plan.json.gz')
DEFAULT_SHAPES = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'k7_shapes_parallel_X26.jsonl')
DEFAULT_SHAREPLAN = os.path.join(ROOT, 'milestones', '37-230-feasibility', 'data', 'c230share.json.gz')
HINTS_PER_DRUP_LINE = 8.8          # milestone 37: 14.7 trimmed full-proof hints per DRUP line x 0.6 replay
SPLIT_HINTS = 20e6                 # SPLIT.md: split above ~20 M core-proof hints

CODE_OF = {(s, s): s for s in range(1, 6)}
CODE_OF.update({(6, 21): 6, (6, 6): 16, (7, 7): 17, (8, 21): 18, (1, 21): 19})
BOUND_OF = {v: k for k, v in CODE_OF.items()}
CH = {1: '1', 2: '2', 3: '3', 4: '4', 5: '5', 6: 'G', 16: '6', 17: '7', 18: 'H', 19: 'F'}
SHARE_CAP = 29                     # corner share of the 7 centres <= 29 is refuted: share >= 30 (README, item 3)
FREE_CODE = 19                     # the free count interval (1, 21) of the share keys


def decode(syms):
    return [BOUND_OF[s] for s in syms]


def name_of(k):
    return 'V' + ''.join(map(str, k[0])) + 'A' + ''.join(CH[s] for s in k[1])


def share_name(k):
    """Module name of a corner-share key (dirs, codes, cap): 'W' + dirs + 'A' + codes + 'K' + cap."""
    return 'W' + ''.join(map(str, k[0])) + 'A' + ''.join(CH[s] for s in k[1]) + 'K' + str(k[2])


def cmd_shareplan(src, out):
    """The 132 corner-share items: every 8-direction (7-centre) shape of the chain, counts free (1, 21),
    statement `RefutedShare (winOf dirs) [(1, 21)] x 7 12 29` (share >= 30 on every such window)."""
    shapes = [json.loads(l)['dirs'] for l in open(src)]
    assert len(shapes) == 132 and all(len(d) == 8 for d in shapes)
    rows = [dict(kind='5', key=[list(d), [FREE_CODE] * 7], level=SHARE_CAP + 1, free=False, est_hints=200000,
                 basis='k7c7-corner') for d in shapes]
    d = dict(summary=dict(target=230, route='K7 corner-share floor: RefutedShare (winOf dirs) [(1,21)]x7 12 29',
                          share=len(rows), source=os.path.relpath(src, ROOT)),
             plain=[], share=rows,
             format=dict(share='kind 5: key [dirs, codes] with code 19 = (1, 21); level = cap + 1'))
    with gzip.GzipFile(out, 'wb', mtime=0) as g:
        g.write(json.dumps(d, separators=(',', ':')).encode())
    print(json.dumps(d['summary']))


# ------------------------------------------------------------------ plan
def cmd_plan(src, out):
    u = json.load(gzip.open(src))
    plain, seen = [], set()
    for w in u:
        codes = [CODE_OF[tuple(b)] for b in w['alpha']]
        key = [list(w['dirs']), codes]
        n = name_of(key)
        assert n not in seen, n
        seen.add(n)
        est = round(w['proof_lines'] * HINTS_PER_DRUP_LINE)
        plain.append(dict(kind='plain', key=key, centres=len(codes), basis='k7c7', free=False, est_hints=est,
                          radius=w['radius'], bounds=[list(b) for b in w['alpha']], case=w['case'],
                          drup_lines=w['proof_lines'], split=est > SPLIT_HINTS))
    plain.sort(key=lambda r: -r['est_hints'])
    d = dict(summary=dict(target=230, route='K7R34C7W16 (relaxed-keller milestone 10), lambda 89/19, D = -15, '
                                         'corner share floor 30 on 7-centre windows',
                          plain=dict(keys=len(plain), paid=len(plain), free=0),
                          est_hints=sum(r['est_hints'] for r in plain),
                          split_items=sum(r['split'] for r in plain),
                          hints_per_drup_line=HINTS_PER_DRUP_LINE, source=os.path.relpath(src, ROOT)),
             plain=plain, share=[],
             format=dict(plain='kind plain: key [dirs, codes] (c230.py: 1..5 exact, 6 = [6,21], 16 = 6, 17 = 7, '
                               '18 = [8,21]); bounds = decoded intervals; radius of the CNF; est_hints = DRUP lines '
                               'x 8.8; split = est above 20 M'))
    with gzip.GzipFile(out, 'wb', mtime=0) as g:
        g.write(json.dumps(d, separators=(',', ':')).encode())
    print(json.dumps(d['summary']))


# ------------------------------------------------------------------ adapter
# Peak RssAnon of the Lean build by merged-source size, for prod435's memory budget (prod435 uses this
# instead of its generic build_gb, which was fit on the 231/232 share/ctx certificates). Upper envelope,
# with 10-20 % margin, of 17,370 published c230 builds (18 Nov): max 0.63 GB at 0.1-0.2 MB of source,
# 0.81 at 0.2-0.5, 1.00 at 1-2, 1.41 at 3-5, 1.37 at 7-10, 1.59 at 15-20, 3.17 at 30-50, 5.25 at
# 75-100, 6.28 at 125-150, 6.30 at 175-260 MB. The generic fit predicted 2-3.5 GB for 5-15 MB sources
# (real <= 1.6), so medium builds queued for memory beside a big one.
BUILD_GB_KNOTS = [(0, 0.3), (0.2, 0.75), (0.5, 0.95), (2, 1.15), (5, 1.55), (10, 1.75), (20, 2.6), (50, 3.9),
                  (100, 6.0), (150, 7.0), (250, 7.6)]


def build_gb(src_bytes):
    m = src_bytes / 1e6
    K = BUILD_GB_KNOTS
    if m >= K[-1][0]:
        return K[-1][1] + 0.0253 * (m - K[-1][0])
    for (x0, y0), (x1, y1) in zip(K, K[1:]):
        if m < x1:
            return y0 + (y1 - y0) * (m - x0) / (x1 - x0)


_PLAN_RADIUS = {}


def _radius_map():
    if not _PLAN_RADIUS:
        p = os.environ.get('C230_PLAN', DEFAULT_PLAN)
        for r in json.load(gzip.open(p))['plain']:
            _PLAN_RADIUS[name_of(r['key'])] = r['radius']
    return _PLAN_RADIUS


def apply():
    """Patch the 4.19 generators (as imported by cert231) for interval keys. Idempotent."""
    for p in (os.path.join(ROOT, 'milestones', '35-231-lean', 'certify'),
              os.path.join(ROOT, 'milestones', '33-233-lean', 'certify'),
              os.path.join(ROOT, 'milestones', '25-k7-234', 'certify'),
              os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')):
        if p not in sys.path:
            sys.path.insert(0, p)
    import cert231
    C = cert231.C
    if getattr(C, '_c230', False):
        return cert231
    GC, K, FK = C.GC, C.K, C.FK
    GC.dir_bounds = lambda syms: decode(syms)
    FK.bound_of = lambda s: BOUND_OF[s]
    C.pname = name_of
    cert231.C.pname = name_of
    orig_sname = C.sname
    C.sname = lambda k: share_name(k) if FREE_CODE in k[1] else orig_sname(k)
    # corner-share keys: the Cnf module states its bounds as the literal intervals (cert233.emit_share writes
    # `boundsOf syms`, whose meaning for code 19 would be (6, 21), a weaker statement)
    orig_emit_share = C.emit_share

    def emit_share(meta, out):
        r = orig_emit_share(meta, out)
        if FREE_CODE in meta['syms']:
            p = os.path.join(out, 'LocalWindowCnf', meta['name'] + '.lean')
            old = 'noncomputable def bounds : List (Nat × Nat) := boundsOf %s' % meta['syms']
            new = 'noncomputable def bounds : List (Nat × Nat) := %s' % (
                '[' + ', '.join('(%d, %d)' % BOUND_OF[x] for x in meta['syms']) + ']')
            t = open(p, encoding='utf-8').read()
            assert t.count(old) == 1, (p, old)
            open(p, 'w', encoding='utf-8').write(t.replace(old, new))
        return r
    C.emit_share = emit_share
    # the radius of the key being processed (one key per cert231 call in prod435): K.encoding reads
    # K.RADIUS at call time
    orig_enc = K.encoding

    def encoding(dirs, syms):
        K.RADIUS = _radius_map()[name_of((tuple(dirs), tuple(syms)))]
        return orig_enc(dirs, syms)
    K.encoding = encoding
    orig_core = C.core_plain

    def core_plain(k, work, certs, cad):
        meta = orig_core(k, work, certs, cad)
        meta['radius'] = _radius_map()[name_of(k)]
        meta['lean_bounds'] = [list(b) for b in decode(k[1])]     # literal bounds in the statement
        meta['cnf_source'] = meta['cnf_source'].replace('radius 4', 'radius %d' % meta['radius'])
        return meta
    C.core_plain = core_plain
    # replay defaults of SPLIT.md: one round, 3 configurations in parallel, genv3stream
    GC.PORTFOLIO = [['--unsat'], ['--unsat', '--subsume=0'], []]
    orig_lrat = GC.core_lrat

    def core_lrat(name, core_ids, work, cadical, seeds, certs=GC.DCERTS, rounds=None, jobs=None):
        return orig_lrat(name, core_ids, work, cadical, [1], certs, rounds=1, jobs=3)
    GC.core_lrat = core_lrat
    C.V3 = os.path.join(HERE, 'genv3stream.py')
    C._c230 = True
    return cert231


def cmd_cert(args):
    apply()
    sys.argv = [os.path.join(HERE, 'cert435.py')] + args
    import runpy
    runpy.run_path(os.path.join(HERE, 'cert435.py'), run_name='__main__')


def cmd_names(plan, min_est):
    for r in json.load(gzip.open(plan))['plain']:
        if r['est_hints'] >= min_est:
            print(name_of(r['key']), r['est_hints'], r['radius'], r['split'])


if __name__ == '__main__':
    if sys.argv[1:2] == ['plan']:
        a = sys.argv[2:]
        src = a[a.index('--src') + 1] if '--src' in a else DEFAULT_SRC
        out = a[a.index('--out') + 1] if '--out' in a else DEFAULT_PLAN
        cmd_plan(src, out)
    elif sys.argv[1:2] == ['cert']:
        cmd_cert(sys.argv[2:])
    elif sys.argv[1:2] == ['shareplan']:
        a = sys.argv[2:]
        cmd_shareplan(a[a.index('--src') + 1] if '--src' in a else DEFAULT_SHAPES,
                      a[a.index('--out') + 1] if '--out' in a else DEFAULT_SHAREPLAN)
    elif sys.argv[1:2] == ['names']:
        a = sys.argv[2:]
        cmd_names(a[0], float(a[a.index('--min-est') + 1]) if '--min-est' in a else 0)
    else:
        raise SystemExit(__doc__)
