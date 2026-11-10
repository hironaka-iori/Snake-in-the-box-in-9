"""Shared pieces of milestone 31 (the certificate cost of the share-weighted k6 chain to 233).

Imports: milestone 28's comb (product, share tables, Bellman-Ford, the arithmetic (*)), milestone 25's
cost model (prune234.Costs: measured replays of data/replay234.jsonl, then the per-(kind, solve-time
bin) means of model234.json, then est_r4, then the class mean of keys without a solve time).

Plain key cost (hints of the Lean replay, core + portfolio pipeline of the 235 build):
  free (236/237/235 replayed) -> measured (m25 replay234 or this milestone's replay233) ->
  bin mean on the key's own solve time (k6loop / m23 / m25 decide234 / m28 oracle_plain, scaled by
  M28_SEC_SCALE for m28's wincert_share-encoded solves, see data/calib233.json) -> est_r4 -> class mean.
Share threshold cost: data/calib233.json (fit on this milestone's replays of share thresholds at
their needed level) applied to the solve time of the cheapest UNSAT call at a level >= the level used.
"""
import sys, os, json, gzip, glob, itertools, math
sys.dont_write_bytecode = True
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '1'
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
D = os.path.join(HERE, 'data')
M28 = os.path.join(MS, '28-combined-identities')
M25 = os.path.join(MS, '25-k7-234')
SCR = os.environ.get('SCR233', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/'
                     '9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/cost233')
os.environ.setdefault('SCR234', SCR)          # cost234's scratch (its FIFO dir) -> ours
sys.path.insert(0, M28)
import comb as C                                # noqa: E402
fp, GA = C.fp, C.GA
sys.path.insert(0, M25)
sys.modules.pop('k7', None)                     # 22-global-arguments/k6_w3 has another k7.py
import k7                                       # noqa: E402
import prune234 as P4                           # noqa: E402
sys.path.insert(0, os.path.join(MS, '23-k6-lean', 'full_product'))
import prune as PR                              # noqa: E402

NC, NT = GA.NC, GA.NT
LUMP = fp.LUMP
REPLAY233 = os.path.join(D, 'replay233.jsonl')
CALIB = os.path.join(D, 'calib233.json')
CERT_SHAPES = {(0, 1, 2, 0, 3, 2), (0, 1, 2, 0, 3, 1), (0, 1, 2, 3, 0, 4), (0, 1, 2, 3, 1, 4)}
# checker v3 (milestone 26): about 0.1 ms per hint (0.2 conservative), about 2.5 B of .olean per hint;
# plus about 50 KB of Cnf/Sat module per certificate (packed core, milestone 26 "Production").
MS_PER_HINT = (0.1, 0.2)
B_PER_HINT = 2.5
KB_PER_CERT = 50.0


def m28_committed(prefix):
    """Milestone 28 data files with this prefix that are committed (the refinement toward 232 writes
    uncommitted files there; only committed data are used)."""
    import subprocess
    import time as _t
    out = []
    for _ in range(20):                         # retry while another agent holds the index
        out = subprocess.run(['git', 'ls-files', os.path.join(M28, 'data')], capture_output=True, text=True,
                             cwd=MS).stdout.split()
        if out:
            break
        _t.sleep(3)
    if not out:
        raise RuntimeError('git ls-files of milestone 28 data failed')
    root = os.path.abspath(os.path.join(MS, '..'))
    fs = [os.path.join(MS, f) for f in out]
    return sorted(f for f in fs if os.path.basename(f).startswith(prefix) and os.path.exists(f))


def jl(f):
    """JSON lines of a file; a milestone-28 file is read as committed (git show HEAD:path)."""
    if f.startswith(M28 + os.sep):
        import subprocess
        rel = os.path.relpath(f, os.path.join(MS, '..'))
        import time as _t
        for _ in range(20):                     # another agent may be committing (index lock): retry
            p = subprocess.run(['git', 'show', f'HEAD:{rel}'], capture_output=True, cwd=MS)
            if p.returncode == 0 and p.stdout:
                break
            _t.sleep(3)
        else:
            raise RuntimeError(f'git show HEAD:{rel} failed: {p.stderr[:200]}')
        raw = p.stdout
        if f.endswith('.gz'):
            raw = gzip.decompress(raw)
        return (json.loads(l) for l in raw.decode().splitlines() if l.strip())
    return (json.loads(l) for l in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)))


def own_plain_unsat28():
    out = []
    for f in m28_committed('oracle_plain'):
        for r in jl(f):
            if r['result'] == 'UNSAT':
                for t in itertools.product(*[C.lumped_choices(a) for a in r['alpha']]):
                    out.append(fp.lkey(tuple(r['dirs']), t))
    return out


def share_records28():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        'refine_share_m11', os.path.join(MS, '11-local-ceiling', 's0_share_loop', 'refine_share.py'))
    RS = importlib.util.module_from_spec(spec); spec.loader.exec_module(RS)
    O = RS.ShareOracle()
    fs = [os.path.join(MS, '11-local-ceiling', 'k6_loop', 'oracle_share.jsonl'),
          os.path.join(MS, '11-local-ceiling', 's0_k6_ceiling', 'oracle5_extra.jsonl')] + m28_committed('oracle_share') + \
        sorted(glob.glob(os.path.join(D, 'oracle_share233*.jsonl')))
    for f in fs:
        for r in jl(f):
            if len(r['alpha']) == 5:
                O.apply(r)
    return O


def log(*a):
    C.log(*a)


def disk_mb():
    return C.disk_mb()


def lk_of(dirs, syms):
    return fp.lkey(tuple(dirs), tuple(syms))


def calib():
    if os.path.exists(CALIB):
        return json.load(open(CALIB))
    return dict(share=dict(A=1.0e6, B=1.0, floor=1.2e4), m28_sec_scale=1.0)


# ------------------------------------------------------------------ plain pool and costs
def plain_pool():
    """Every known plain-UNSAT lumped k6 key: fp.Status + milestone 28's own (committed) calls +
    milestone 25's k7.status and decide234 k6 keys."""
    S = fp.Status()
    ks = set(S.unsat()) | set(own_plain_unsat28())
    try:
        ks |= set(k7.status().unsat())
    except Exception as e:                       # pragma: no cover
        log('k7.status failed', e)
    ks |= set(P4.extra_k6())
    return sorted(ks)


def m28_seconds():
    sec = {}
    for f in m28_committed('oracle_plain'):
        for r in jl(f):
            if r['result'] == 'UNSAT':
                k = PR.lumped_of(r['dirs'], r['alpha'])
                if k:
                    sec[k] = float(r['seconds'])
    return sec


def measured233():
    out = {}
    if os.path.exists(REPLAY233):
        for l in open(REPLAY233):
            r = json.loads(l)
            if r.get('hints') is not None and r.get('kind') == 'k6':
                out[lk_of(r['dirs'], r['syms'])] = r
    return out


class PlainCosts:
    def __init__(self):
        self.C4 = P4.Costs(ovh=0.0)
        self.m28 = m28_seconds()
        self.me = measured233()
        self.scale = calib().get('m28_sec_scale', 1.0)

    def __call__(self, k):
        """(hints, core clauses, basis)."""
        if k in self.C4.free:
            return 0.0, 0.0, 'reuse'
        r = self.me.get(k)
        if r is not None:
            return float(r['hints']), float(r['core']), 'measured'
        h, c, b = self.C4.k6(k)
        if b.startswith('median') and k in self.m28:
            t = self.m28[k] * self.scale
            n = len(k[1])
            fb = (1.49e6 * max(t, 0.01) ** 0.843, 2000.0, 'fit')
            h, c, bb = self.C4.cls(f'k6_{n}_{P4.sbin(t)}', fb)
            b = 'm28sec_' + bb
        return h, c, b


# ------------------------------------------------------------------ share data
def share_lb():
    """Lumped 5-key -> proved share lower bound (every share oracle: milestone 11 incl. E1 seeds,
    milestone 28's committed calls), and lumped 5-key -> UNSAT calls [(T, seconds or None)]."""
    O = share_records28()
    lb = {}
    for (ds, al), s in O.st.items():
        if s['lb'] <= 0 or len(al) != 5:
            continue
        for t in itertools.product(*[C.lumped_choices(a) for a in al]):
            k = lk_of(ds, t)
            lb[k] = max(lb.get(k, 0), s['lb'])
    calls = {}
    files = [os.path.join(MS, '11-local-ceiling', 's0_share_loop', 'share_oracle.jsonl'),
             os.path.join(MS, '11-local-ceiling', 'k6_loop', 'oracle_share.jsonl'),
             os.path.join(MS, '11-local-ceiling', 's0_k6_ceiling', 'oracle5_extra.jsonl')] + \
        m28_committed('oracle_share') + sorted(glob.glob(os.path.join(D, 'oracle_share233*.jsonl')))
    for f in files:
        if not os.path.exists(f):
            continue
        for r in jl(f):
            if r.get('kind') == 'thr' and r['result'] == 'UNSAT' and len(r['alpha']) == 5:
                for t in itertools.product(*[C.lumped_choices(a) for a in r['alpha']]):
                    k = lk_of(r['dirs'], t)
                    calls.setdefault(k, []).append((int(r['T']), r.get('seconds')))
                    lb[k] = max(lb.get(k, 0), int(r['T']))
    return lb, calls


def share_floor():
    """Lumped 5-key -> level proved universally in Lean on origin/main (milestones 73/152/155)."""
    F = {}
    for c, al, v in C.CERT_SHARE:
        for t in itertools.product(*[C.lumped_choices(a) for a in al]):
            k = lk_of(c, t)
            F[k] = max(F.get(k, 0), v)
    return F


def share_hints(sec, cal=None):
    cal = cal or calib()['share']
    if sec is None:
        return None
    return max(cal['floor'], cal['A'] * max(sec, 1e-3) ** cal['B'])


def best_pq(lam, qmax=64, bmin=6):
    """P/Q <= lam (in weight units, 120 per alpha unit) and potential bits B with
    2^B - 1 <= 227 P - 117000 Q - 1 (then m <= 233 by (*)), maximising the slack (2^B - 1)/Q."""
    best = None
    for Q in range(1, qmax + 1):
        P = int(math.floor(lam * Q))
        g = 227 * P - 117000 * Q
        if g < 2:
            continue
        B = (g).bit_length() - 1
        if 2 ** B - 1 >= g:
            B -= 1
        sl = (2 ** B - 1) / Q
        if best is None or sl > best[3] + 1e-12:
            best = (P, Q, B, sl)
    return best


def bound233(P, Q, B):
    """m bound of (*) with R = 2^B - 1 (a = 1, b = 0)."""
    return int(C.bound_m(P, Q, 2 ** B - 1, 1, 0, 0))


def summary_cost(hints, ncert):
    return dict(hints=round(hints), certificates=ncert,
                kernel_hours_0p1ms=round(hints * MS_PER_HINT[0] * 1e-3 / 3600, 1),
                kernel_hours_0p2ms=round(hints * MS_PER_HINT[1] * 1e-3 / 3600, 1),
                olean_GB_hints=round(hints * B_PER_HINT / 1e9, 2),
                cnf_modules_GB=round(ncert * KB_PER_CERT / 1e6, 2))
