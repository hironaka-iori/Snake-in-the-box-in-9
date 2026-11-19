import sys, json
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '32-forest-density-lp', 'scripts'))
from fractions import Fraction
import forestlp
for n in (7,8,9):
    M = forestlp.build(n, 4)
    for c in (1,):
        eps = Fraction(2*c, 2**n)
        val, rd, x = forestlp.solve(M, float(eps))
        cert, yE, worst = forestlp.certify(M, rd, [eps])
        b = cert[eps]*2**n
        print(json.dumps(dict(n=n,c=c,lp=val*2**n,exact=str(b),floor=int(b//1))), flush=True)
