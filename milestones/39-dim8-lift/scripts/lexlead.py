"""Append lex-leader clauses for the stabiliser of the fixed copy A (inside B6 on the low coordinates,
times the swap of coordinates 6 and 7) to a cube CNF.  Sound: the lex-least image of a solution under
the stabiliser satisfies every added constraint S <=_lex g(S) (vertex order 64, 65, ..., 255).
usage: python3 lexlead.py in.cnf Ahex out.cnf maxelems"""
import sys, itertools, random
fin, Ahex, fout, maxe = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
A = int(Ahex, 16); As = {u for u in range(64) if A >> u & 1}
G = []
for p in itertools.permutations(range(6)):
    pm = [sum(1 << p[i] for i in range(6) if u >> i & 1) for u in range(64)]
    for t in range(64):
        if all((pm[u] ^ t) in As for u in As):
            G.append((pm, t))
els = []
for (pm, t) in G:
    for sw in (0, 1):
        if sw == 0 and t == 0 and pm == list(range(64)): continue
        def g(u, pm=pm, t=t, sw=sw):
            lo, hi = u & 63, u >> 6
            if sw: hi = ((hi & 1) << 1) | (hi >> 1)
            return (pm[lo] ^ t) | (hi << 6)
        els.append(g)
random.seed(1); random.shuffle(els); els = els[:maxe]
print('stabiliser', len(G), 'elements used', len(els))
hdr = open(fin).readline().split(); nv, nc = int(hdr[2]), int(hdr[3])
add = []
for g in els:
    # S <=_lex S o g^{-1}: position u compares x_u = s(u) with y_u = s(g^{-1} u); g is a bijection so use inverse
    inv = {g(u): u for u in range(256)}
    prev = None
    for u in range(64, 256):
        x, y = u + 1, inv[u] + 1
        if x == y: continue
        pre = [] if prev is None else [-prev]
        add.append(pre + [-x, y])
        nv += 1; e = nv
        add.append(pre + [x, y, e]); add.append(pre + [-x, -y, e])
        prev = e
with open(fout, 'w') as f:
    f.write('p cnf %d %d\n' % (nv, nc + len(add)))
    with open(fin) as g0:
        next(g0)
        for l in g0: f.write(l)
    for c in add: f.write(' '.join(map(str, c)) + ' 0\n')
print('added', len(add))
