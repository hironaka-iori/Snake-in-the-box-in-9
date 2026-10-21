"""Q9 = Q5 x Q4 walks of the Q8-record type: two images of the Q8 record's
Q3 walk W joined across light bit 3 (single crossing).  Classes are taken
modulo parity-preserving symmetries of Q4 (coordinate permutations of Q3,
even translations) and reversal of the whole walk."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import itertools
W=[0,2,3,7,3,1,0,4,5,7,5,1,0,4,6,2,6]
def pc(x): return bin(x).count('1')
def q3auts():
    out=[]
    for p in itertools.permutations(range(3)):
        for t in range(8):
            out.append((p,t))
    return out
def ap(a,c):
    p,t=a; return sum(((c>>i)&1)<<p[i] for i in range(3))^t
def images(w):
    S=set()
    for a in q3auts():
        v=tuple(ap(a,c) for c in w); S.add(v); S.add(v[::-1])
    return sorted(S)
def canon(walk):
    # parity-preserving Q4 syms: perms of 4 coords, even translations; reversal
    best=None
    for p in itertools.permutations(range(4)):
        for t in range(16):
            if pc(t)%2: continue
            v=tuple(sum(((c>>i)&1)<<p[i] for i in range(4))^t for c in walk)
            for u in (v,v[::-1]):
                if best is None or u<best: best=u
    return best
def doubling():
    I=images(W); seen=set(); out=[]
    for a in I:
        for b in I:
            if a[-1]!=b[0]: continue
            w=list(a)+[c|8 for c in b]
            cw=canon(w)
            if cw in seen: continue
            seen.add(cw); out.append(w)
    return out
if __name__=='__main__':
    D=doubling(); print(len(images(W)),len(D))
