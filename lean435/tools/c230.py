#!/usr/bin/env python3
"""Certificates of the K7 cap-7 route to m <= 230 (milestone 37): window exclusions with arbitrary
count INTERVALS and radius 3 or 4, produced by the unchanged prod435 / cert231 / cert233 plain-key
pipeline through a small adapter.

    c230.py plan [--src milestones/37-230-feasibility/data/k7_uncovered.json.gz] [--out PLAN]
    c230.py cert STEP [cert231 args...]      (what prod435 runs instead of cert435.py; PROD435_CERT)
    c230.py names PLAN [--min-est H]         list the plan's module names (largest first)

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
HINTS_PER_DRUP_LINE = 8.8          # milestone 37: 14.7 trimmed full-proof hints per DRUP line x 0.6 replay
SPLIT_HINTS = 20e6                 # SPLIT.md: split above ~20 M core-proof hints

CODE_OF = {(s, s): s for s in range(1, 6)}
CODE_OF.update({(6, 21): 6, (6, 6): 16, (7, 7): 17, (8, 21): 18})
BOUND_OF = {v: k for k, v in CODE_OF.items()}
CH = {1: '1', 2: '2', 3: '3', 4: '4', 5: '5', 6: 'G', 16: '6', 17: '7', 18: 'H'}


def decode(syms):
    return [BOUND_OF[s] for s in syms]


def name_of(k):
    return 'V' + ''.join(map(str, k[0])) + 'A' + ''.join(CH[s] for s in k[1])


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
    elif sys.argv[1:2] == ['names']:
        a = sys.argv[2:]
        cmd_names(a[0], float(a[a.index('--min-est') + 1]) if '--min-est' in a else 0)
    else:
        raise SystemExit(__doc__)
