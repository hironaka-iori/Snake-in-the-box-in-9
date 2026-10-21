"""Ceiling check: do the fibre-union adversaries of milestone 11 pass every radius-4 window?

For each adversary (a union of induced cycles) and each window of k consecutive centres along a
cycle, the adversary's own selection S cap B is tested against the W3 base CNF (no cap) under
assumptions.  If every window passes, the adversary walks a cycle of the window automaton whose
windows all have SAT witnesses (a window fails if the clauses reject the selection or if a whole
cycle of the adversary lies inside the ball, which the lazy cycle cuts exclude) with charge = the adversary's window charge, so no certificate
set of this window family can prove a mean charge above the adversary's mean:
    ceiling  m <= 63148 / mean_c + 5     (the rigorous formula of shape_aut / README)
usage: adv_check.py [k ...]
"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import w3enc
from pysat.solvers import Cadical153

ADV = os.path.join(HERE, '..', '..', '11-local-ceiling', 'data')


def main():
    ks = [int(x) for x in sys.argv[1:]] or [5]
    out = {}
    for nm in ('adversary224', 'adversary208'):
        d = json.load(open(os.path.join(ADV, nm + '.json')))
        S = d['S']
        cs = {x: w3enc.charge(S, x) for x in S}
        mean = sum(cs.values()) / len(S)
        res = dict(v=len(S), mean_c=mean, mean_w3=mean / 12, min_c=min(cs.values()),
                   census_total=sum(cs.values()), ceiling_m=63148 / mean + 5)
        for k in ks:
            seen, npass, nfail, ncyc = set(), 0, 0, 0
            for c in d['cycles']:
                L = len(c)
                for st in range(L):
                    vs = [c[(st + i) % L] for i in range(k + 2)]
                    z = vs[0]
                    win = [x ^ z for x in vs]
                    Sz = set(x ^ z for x in S)
                    enc = w3enc.W3Encoding(win, None, 4, None, sym=False)
                    assum = [enc.var[v] if v in Sz else -enc.var[v] for v in enc.ball]
                    with Cadical153(bootstrap_with=enc.clauses) as s:
                        ok = s.solve(assumptions=assum)
                    if ok:
                        # induced cycles inside the ball would be cut: check
                        sel = [v for v in enc.ball if v in Sz]
                        cyc = w3enc.cycles_of(sel)
                        ncyc += bool(cyc)
                        ok = not cyc
                    npass += ok; nfail += not ok
            res[f'k{k}'] = dict(windows=npass + nfail, passed=npass, failed=nfail,
                                failed_whole_cycle_in_ball=ncyc)
        out[nm] = res
        print(nm, json.dumps(res), flush=True)
    json.dump(out, open(os.path.join(HERE, 'data', 'adversary_ceiling.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
