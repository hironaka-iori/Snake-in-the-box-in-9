"""Write milestone 29's level-encoded CNF (gforest.encode) as DIMACS, optionally with a fixed block.
usage: python3 dimacs29.py n c L out.cnf [--fix k file.json]   (fix: copy 0 of Q_k fixed, others <= |A|)"""
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '29-q8-layering', 'scripts'))
import gforest
from pysat.card import CardEnc, EncType
n, c, L = map(int, sys.argv[1:4]); out = sys.argv[4]
D = int(sys.argv[sys.argv.index('--D') + 1]) if '--D' in sys.argv else 1 << (n - 2)
pool, s, cl = gforest.encode(n, c, L, levels=D, sym='--nosym' not in sys.argv)
if '--fix' in sys.argv:
    i = sys.argv.index('--fix'); k = int(sys.argv[i + 1]); A = set(json.load(open(sys.argv[i + 2])))
    for x in range(1 << k):
        cl.append([s[x]] if x in A else [-s[x]])
    for t in range(1, 1 << (n - k)):
        lits = [s[(t << k) | x] for x in range(1 << k)]
        card = CardEnc.atmost(lits, bound=len(A), top_id=pool.top, encoding=EncType.seqcounter)
        cl += card.clauses; pool.top = max(pool.top, card.nv)
if '--allmax' in sys.argv:
    # the fixed copy is a largest k-subcube over every choice of k directions (WLOG): all k-subcubes <= |A|
    from itertools import combinations
    for dirs in combinations(range(n), k):
        msk = sum(1 << d for d in dirs)
        for base in range(1 << n):
            if base & msk: continue
            if msk == (1 << k) - 1: continue      # the parallel class of the fixed copy is done above
            lits = [s[u] for u in range(1 << n) if (u & ~msk) == base]
            card = CardEnc.atmost(lits, bound=len(A), top_id=pool.top, encoding=EncType.seqcounter)
            cl += card.clauses; pool.top = max(pool.top, card.nv)
nv = max(pool.top, max(abs(x) for C in cl for x in C))
with open(out, 'w') as f:
    f.write('p cnf %d %d\n' % (nv, len(cl)))
    for C in cl:
        f.write(' '.join(map(str, C)) + ' 0\n')
print(out, nv, len(cl))
