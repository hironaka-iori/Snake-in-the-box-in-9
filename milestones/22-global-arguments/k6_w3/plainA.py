"""(b) The converged plain k6 route (A of ../../11-local-ceiling/k6_loop, mu = 65/16): w_3 charges on
its minimum cycle.  Rebuilds the minimum sym-mean cycle with every plain exclusion now known, then
runs the exact-minimum w_3 search (w3survey.search, symmetry breaking on) on each distinct 5-window
and, with 'k6', each distinct 6-window.  Results: data/w3_k6_oracle.jsonl, data/plainA_cycle.json.
usage: plainA.py [k6] [KEYSEC]"""
import sys, os, json, time
from fractions import Fraction as Fr
from k6w3lib import *
from ceil import setup


def main():
    do6 = 'k6' in sys.argv
    keysec = float(sys.argv[-1]) if sys.argv[-1].replace('.', '').isdigit() else 300
    G, P, O, sub = setup()
    b5, b6 = masks(G, P)
    keep = ~b5[G['K5']] & ~b6[G['K6']]
    idx = live(G, keep)
    w = G['S'][idx].astype(np.int64)
    _, cyc = howard(G['n6'], G['U'][idx], G['V'][idx], w)
    ce = [int(idx[e]) for e in cyc]
    lam = Fr(int(w[cyc].sum()), len(cyc))
    k5 = [G['keys5'][G['K5'][e]] for e in ce]; k6 = [G['keys6'][G['K6'][e]] for e in ce]
    print('plain mean', lam, float(lam), 'len', len(ce), flush=True)
    todo = list(dict.fromkeys(k5)) + (list(dict.fromkeys(k6)) if do6 else [])
    for k in todo:
        s = O.get(k)
        if s['ub'] is not None and s['lb'] >= s['ub']:
            continue
        fl = sub.floor5(k) if len(k[1]) == 5 else 0
        survey.search(k, O, 120, keysec, fl, verbose=True)
        s = O.get(k); print(f'  {keystr(k)}: lb {s["lb"]} ub {s["ub"]} rss {rss_mb():.0f}', flush=True)
    rows = []
    for e, a, b in zip(ce, k5, k6):
        sa, sb = O.get(a), O.get(b)
        rows.append(dict(sym=int(G['S'][e]), k5=keystr(a), lb5=sa['lb'], ub5=sa['ub'], k6=keystr(b),
                         plain6=P.st.get(b), lb6=sb['lb'], ub6=sb['ub']))
    res = dict(mean_sym=str(lam), len=len(ce), rows=rows)
    for nm, kk, d in (('5', 'lb5', 5), ('5', 'ub5', 5), ('6', 'lb6', 6), ('6', 'ub6', 6)):
        v = [r[kk] for r in rows]
        if all(x is not None and x > 0 for x in v):
            mu = sum(v) / len(v) / d
            res[f'mu_{kk}'] = mu; res[f'm_{kk}'] = mbound(mu)
    json.dump(res, open(os.path.join(DATA, 'plainA_cycle.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != 'rows'}), flush=True)


if __name__ == '__main__':
    main()
