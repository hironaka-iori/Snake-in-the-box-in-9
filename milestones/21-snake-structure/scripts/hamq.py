# enumerate Hamiltonian paths of Q_k up to symmetry (start at 0)
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
from itertools import permutations
import sys
def ham(k):
    n=1<<k; res=set()
    def canon(p):
        best=None
        for perm in permutations(range(k)):
            for rev in (p,p[::-1]):
                t=rev[0]
                q=tuple(sum((((x^t)>>i)&1)<<perm[i] for i in range(k)) for x in rev)
                if best is None or q<best: best=q
        return best
    path=[0]; used={0}
    def rec():
        if len(path)==n:
            res.add(canon(path)); return
        for d in range(k):
            y=path[-1]^(1<<d)
            if y not in used:
                used.add(y); path.append(y); rec(); path.pop(); used.discard(y)
    rec(); return sorted(res)
if __name__=='__main__':
    k=int(sys.argv[1]); H=ham(k); print(len(H))
    for h in H: print(h)
