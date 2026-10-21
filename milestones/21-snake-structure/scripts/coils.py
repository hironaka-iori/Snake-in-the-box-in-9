# induced cycles (coils) of Q5 with 14 vertices; containment of spines and bank pieces
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
from common import *
from bankwalk import quotient
from palette import bank_palette
from collections import Counter
h=5; N=32
NB=[[x^(1<<d) for d in range(h)] for x in range(N)]
coils=set()
def rec(path,S):
    x=path[-1]
    for y in NB[x]:
        if y==path[0] and len(path)>=4:
            # closing: check y adjacent only to path[1], x
            coils.add(frozenset(path)); continue
        if y in S: continue
        # y adjacent to path vertices other than x? allow path[0] only (closing later)
        bad=[z for z in NB[y] if z in S and z!=x]
        if bad and not (bad==[path[0]] ): continue
        if bad==[path[0]] and len(path)+1<14: continue
        path.append(y); S.add(y)
        if len(path)<=14: rec(path,S)
        path.pop(); S.discard(y)
for s in [0]:
    rec([0],{0})
c14=[c for c in coils if len(c)==14]
# verify induced and translate to all
allc=set()
for c in c14:
    for t in range(32): allc.add(frozenset(x^t for x in c))
allc=[c for c in allc if all(sum(1 for y in NB[x] if y in c)==2 for x in c)]
print('induced 14-coils of Q5 (all translates):',len(allc), 'lengths found',Counter(len(c) for c in coils))
b=load()
res=Counter(); spine=Counter()
for idx in range(0,127):
    e=b[idx]; A,B,cell,hv=bank_palette(e); seq,sizes,L,H=quotient(e,4)
    spine[(any(A<=c for c in allc), any(B<=c for c in allc))]+=1
    vs=e['vertex_sequence']; i=0
    for c,s in zip(seq,sizes):
        piece=frozenset(hv(v) for v in vs[i:i+s]); i+=s
        if s>=12: res[(s, any(piece<=cc for cc in allc))]+=1
print('spines inside a coil (A,B):',spine)
print('pieces >=12 inside a 14-coil:',sorted(res.items()))
