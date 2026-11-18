#!/usr/bin/env python3
"""Decode the rows of the K7 chain tables (sfwd/srev of WindowAutomatonK7R34C7W16Tab.lean, ofGaps
literals) and the window shape index (Base), for the Python pre-check of c230gen.py.
    c230tabs.py SRCDIR OUT.pkl"""
import re, json, sys, os, pickle
RK = sys.argv[1]
def b64v(c):
    if 65<=c<=90: return c-65
    if 97<=c<=122: return c-71
    if 48<=c<=57: return c+4
    return 62 if c==43 else 63
def gaps(s):
    out=[];cur=0;sh=0;last=0;first=True
    for ch in s.encode():
        v=b64v(ch); cur |= (v%32)<<sh
        if v<32:
            p = cur if first else last+cur+1
            out.append(p); last=p; first=False; cur=0; sh=0
        else: sh+=5
    return out
tab=open(os.path.join(RK,'WindowAutomatonK7R34C7W16Tab.lean')).read()
rows={}
for m in re.finditer(r'^def (sfwd|srev)K7R34C7W16v(\d+)_(\d+) : Nat := (.*)$', tab, re.M):
    kind,c,w,rhs=m.group(1),int(m.group(2)),int(m.group(3)),m.group(4)
    g=re.match(r'nat_lit% ofGaps "(.*)"$', rhs)
    if g: bits=gaps(g.group(1))
    else:
        assert re.fullmatch(r'\d+',rhs), rhs[:80]
        n=int(rhs); bits=[i for i in range(n.bit_length()) if n>>i&1]
    rows[(kind,c,w)]=bits
base=open(os.path.join(RK,'WindowAutomatonK7R34C7W16Base.lean')).read()
wm=re.search(r'def wshapeIdxK7R34C7W16 \(c : Nat\) : Nat :=\n(.*?)\n  (\d+)\n', base, re.S)
widx={int(a):int(b) for a,b in re.findall(r'if c = (\d+) then (\d+) else', wm.group(1))}
print('default', wm.group(2), 'n', len(widx))
pickle.dump((rows,widx), open(sys.argv[2],'wb'))
nonhi=sum(1 for b in rows.values() for x in b if x%16!=15)
print(len(rows), 'rows; bits', sum(len(b) for b in rows.values()), 'non-15 bits', nonhi)
from collections import Counter
print(Counter((k[0],k[1]) for k in rows))
