"""Collect the critical / ceiling cycles saved in the repo as cyclic walks of 7-shapes.

Writes data/cycles.json: {name: {"states": [7-shape, ...] (minimal shape period),
"source": ..., "note": ...}}.  The 236/237 automata's own minimum cycles are recomputed
from the certified key sets with refine.Automaton(7, 5, 5) + Howard, as
gen_lean_automaton5.py does.  Cycles saved only as window keys (canonical up to reversal)
are reconstructed as the unique cycle of the 34-shape graph whose consecutive 7-windows have
those keys.

  python collect.py            (about 2 minutes, mostly the two k5 automata)
"""
import json, os, sys
import numpy as np
from shapes import canon, minimal_period

HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
from refine import Automaton, prune, howard, induced  # noqa: E402


def shape_graph():
    sh = sorted({canon(ds) for ds in __import__('itertools').product(range(7), repeat=7)
                 if induced(canon(ds))})
    succ = {c: set() for c in sh}
    for c in sh:
        for d in range(min(max(c) + 2, 9)):
            ds = c + (d,)
            if induced(ds):
                succ[c].add(canon(ds[1:]))
    return sh, succ


SH, SUCC = shape_graph()


def kcanon(ds):
    return min(canon(ds), canon(tuple(reversed(ds))))


def from_keys7(keys):
    """Cycles of shapes s_0..s_{p-1} with kcanon(s_i) = keys[i] (keys of the target states)."""
    p = len(keys)
    out = []

    def go(path):
        if len(path) == p:
            if path[0] in SUCC[path[-1]]:
                out.append(list(path))
            return
        for t in sorted(SUCC[path[-1]]):
            if kcanon(t) == keys[len(path)]:
                go(path + [t])
    for s in SH:
        if kcanon(s) == keys[0]:
            go([s])
    return out


def rot_min(states):
    q = minimal_period(states)
    st = [tuple(s) for s in states[:q]]
    return min(st[i:] + st[:i] for i in range(q))


def k5_cycle(index):
    cases = [c for c in json.load(open(index))['cases'] if c['drat_trim_verified']]
    keys = set()
    from refine import key
    for c in cases:
        keys.add(key(tuple(c['dirs']), tuple(tuple(a) for a in c['alpha'])))

    class L:
        def status(self, k):
            return 'UNSAT' if k in keys else None
    A = Automaton(7, 5, 5)
    U, V, W, _ = A.edges(L())
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
    inv = {v: k for k, v in A.sid.items()}
    from fractions import Fraction as Fr
    lam = Fr(int(W[cyc].sum()), len(cyc))
    states = [inv[int(U[e])][0] for e in cyc]
    counts = [int(W[e]) for e in cyc]
    return states, counts, lam


def main():
    out = {}

    def add(name, states, source, **kw):
        st = rot_min(states)
        out[name] = dict(states=[list(s) for s in st], period=len(st), source=source, **kw)
        print(name, len(st), st, flush=True)

    # keys_235: the lambda = 4 critical 3-cycle (counts 6, 1, 5)
    r = json.load(open(os.path.join(MS, '23-k6-lean/share_bonus/results.json')))
    c = r['keys_235']['mcm'][0]
    add('k6_keys235_lambda4', [tuple(json.loads(s)) for s in c['shapes']],
        '23-k6-lean/share_bonus/results.json keys_235 (= full_product README)', counts=c['counts'],
        mean='4')
    # all known keys: the 16-walk of mean 4.0625 (shape period 8)
    ob = json.load(open(os.path.join(MS, '23-k6-lean/share_bonus/obstruction_B6.json')))
    add('k6_allknown_4.0625', [tuple(e['dirs8'][:7]) for e in ob['edges']],
        '23-k6-lean/share_bonus/obstruction_B6.json', mean='65/16', walk_length=16)
    # the 31/8 8-cycle of the 3,103-key k6_loop set
    k6a = json.load(open(os.path.join(MS, '23-k6-lean/data/k6A_full_product.json')))
    add('k6A_31_8', [tuple(json.loads(s[0])) for s in k6a['cycle_states']],
        '23-k6-lean/data/k6A_full_product.json (README 31/8)', counts=k6a['cycle_new_counts'],
        mean='31/8')
    # share loop period-3 ceiling cycle (all alpha = 4); the w3_survey 8497/6 ceiling has the
    # same shape cycle (k6_w3 README: its unique lift has 6-windows 0123014 / 0123042)
    add('k5_share_ceiling_p3', [(0, 1, 2, 3, 4, 1, 2), (0, 1, 2, 3, 0, 1, 4), (0, 1, 2, 3, 0, 4, 2)],
        '11-local-ceiling/s0_k6_ceiling README sec. 1 (also w3_survey 8497/6 via k6_w3)',
        mean='4 (alpha), 4.7194 with shares')
    # s0_k6_ceiling rigorous 14-cycle (keys6 are the target 7-windows, up to reversal)
    rc = json.load(open(os.path.join(MS, '11-local-ceiling/s0_k6_ceiling/rigorous_ceiling.json')))
    ks = [tuple(k[0]) for k in rc['k5share']['keys6']]
    cand = from_keys7(ks)
    assert cand, 'rigorous 14-cycle not reconstructed'
    for i, cy in enumerate({tuple(rot_min(c)) for c in cand}):
        add(f'k5_share_rigorous14_{i}', list(cy), '11-local-ceiling/s0_k6_ceiling/rigorous_ceiling.json',
            syms=rc['k5share']['syms'])
    # k6_w3 next binding period-6 cycle (k7_F1420p300.json): 6-window keys
    k7 = json.load(open(os.path.join(MS, '22-global-arguments/k6_w3/data/k7_F1420p300.json')))
    ks = [tuple(int(ch) for ch in s.split('/')[0]) for s in k7['cycle']]
    cand = from_keys7(ks)
    assert cand
    for i, cy in enumerate({tuple(rot_min(c)) for c in cand}):
        add(f'k6w3_next_p6_{i}', list(cy), '22-global-arguments/k6_w3/data/k7_F1420p300.json')
    # plain k6 A-route 65/16 cycle (plainA_cycle.json)
    pa = json.load(open(os.path.join(MS, '22-global-arguments/k6_w3/data/plainA_cycle.json')))
    ks = [tuple(int(ch) for ch in r_['k6'].split('/')[0]) for r_ in pa['rows']]
    cand = from_keys7(ks)
    for i, cy in enumerate({tuple(rot_min(c)) for c in cand}):
        add(f'k6plainA_65_16_{i}', list(cy), '22-global-arguments/k6_w3/data/plainA_cycle.json')
    # the 237 and 236 automata (k5, radius 4): their own minimum cycles
    for tag, f in (('237_r4b', 'direction_certificates_r4b.json'), ('236_r4c', 'direction_certificates_r4c.json')):
        st, cn, lam = k5_cycle(os.path.join(MS, '10-window-aggregate/data', f))
        add(f'k5_{tag}', st, f'10-window-aggregate/data/{f} (recomputed, Howard)', counts=cn,
            mean=str(lam), walk_length=len(st))
    os.makedirs(os.path.join(HERE, 'data'), exist_ok=True)
    json.dump(out, open(os.path.join(HERE, 'data', 'cycles.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
