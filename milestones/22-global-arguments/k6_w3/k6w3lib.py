"""Shared loaders for the k6 + w_3 experiments.

Graph: the radius-4 L7 k6 K5 automaton of ../../11-local-ceiling/k6_loop (k5 edges lifted by one
more remembered count; every edge carries a 5-window key and a 6-window key).
Plain statuses: k6loop.Plain (every radius-4 plain oracle of milestones 10/11, alpha-conditioned).
w_3 statuses of 5-windows: ../w3_survey/data/w3_alpha_oracle.jsonl (lb = proved threshold,
ub = exact charge of a SAT witness) plus our own calls in data/w3_k6_oracle.jsonl, which also
holds the 6-window w_3 calls (same record format as w3survey.Oracle).
Charge units: c(x) = sum_Q floor(12/|Q cap S|) (12 c = 1 w_3); bound m <= 7 + 63148/mu,
mu = per-vertex mean of c (w3_survey README; the k = 6 boundary terms differ by < 0.1 edge).
"""
import sys, os, json, time
sys.dont_write_bytecode = True
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.join(HERE, '..', '..')
sys.path.insert(0, os.path.join(MS, '11-local-ceiling', 'k6_loop'))
sys.path.insert(0, os.path.join(MS, '22-global-arguments', 'w3_survey'))
import numpy as np
import k6loop
from k6loop import build, Plain, live, masks
from refine import howard, exact_check
import w3survey as survey
import w3enc

DATA = os.path.join(HERE, 'data')
OW3 = os.path.join(DATA, 'w3_k6_oracle.jsonl')
INF = 10 ** 6


def mbound(mu):
    return 7 + 63148 / mu


def rss_mb():
    for l in open('/proc/self/status'):
        if l.startswith('VmRSS'):
            return int(l.split()[1]) / 1024


def load_w3():
    """Merged w_3 oracle: survey.Oracle semantics (lb, ub, fail, excl) over both files."""
    O = survey.Oracle(OW3)                      # ours (new calls are logged here)
    for l in open(os.path.join(MS, '22-global-arguments', 'w3_survey', 'data', 'w3_alpha_oracle.jsonl')):
        r = json.loads(l)
        k = survey.key(tuple(r['dirs']), r['alpha'])
        s = O.get(k)
        if r['result'] == 'UNSAT':
            s['lb'] = max(s['lb'], r['T'])
        elif r['result'] == 'SAT' and r.get('witness') is not None:
            s['ub'] = r['witness'] if s['ub'] is None else min(s['ub'], r['witness'])
        elif r['result'] == 'TIMEOUT':
            s['fail'] = r['T'] if s['fail'] is None else min(s['fail'], r['T'])
    return O


def arrays5(G, O, sub=None):
    lb = np.zeros(len(G['keys5']), np.int64); ub = np.full(len(G['keys5']), INF, np.int64)
    for i, k in enumerate(G['keys5']):
        s = O.st.get(k)
        f = sub.floor5(k) if sub is not None else 0
        lb[i] = max(s['lb'] if s else 0, f)
        if s and s['ub'] is not None:
            ub[i] = s['ub']
    return lb, ub


def keystr(k):
    return f"{''.join(map(str, k[0]))}/{','.join(str(a[0]) if a[0] == a[1] else str(a[0]) + '+' for a in k[1])}"
