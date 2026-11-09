"""Solve the k = 4 local LPs (hypergeometric version forestlp.py and tagged version taglp.py)
for n = 5..8, and turn each floating dual into an exact rational bound (certify): with y rounded
to rationals and yE >= 0, the bound max_tau [obj - yE*end - y.M] + yE*eps is valid for every LP
feasible point, hence for every induced linear forest with <= c paths.

usage: python3 run_lp.py [hyper|tagged] n1 n2 ...   -> appends JSON lines to ../data/lp_k4.jsonl
"""
import sys, json, os
from fractions import Fraction
import forestlp, taglp

kind = sys.argv[1]
out = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'lp_k4.jsonl'), 'a')
for n in map(int, sys.argv[2:]):
    M = (forestlp.build if kind == 'hyper' else taglp.build)(n, 4)
    for c in list(range(0, 17)) + ([20, 24, 32] if n == 8 else []):
        if 2 * c > 2 ** (n - 1):
            break
        eps = Fraction(2 * c, 2 ** n)
        val, rd, x = forestlp.solve(M, float(eps))
        cert, yE, worst = forestlp.certify(M, rd, [eps])
        b = cert[eps] * 2 ** n
        rec = dict(kind=kind, n=n, k=4, c=c, patterns=len(M['reps']), rows=len(M['rows']),
                   lp_float=round(val * 2 ** n, 6), exact_bound=str(b), exact_bound_float=round(float(b), 6),
                   floor=int(b // 1))
        print(json.dumps(rec), flush=True)
        out.write(json.dumps(rec) + '\n')
