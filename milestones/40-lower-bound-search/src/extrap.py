#!/usr/bin/env python3
"""Part (B): extrapolate ln N(L) (directed snakes, Wang-Landau) to ln(2^n n!) = one orbit.
Validation: in Q5..Q8 use only data up to a fraction f of the known optimum (Q9 data reach
143/191 = 0.75), fit a polynomial of degree d on [Lpeak, Lcut], report the crossing."""
import math, numpy as np
OPT = {5: 13, 6: 26, 7: 50, 8: 98}
def load(n):
    f = 'logs/exact_q5.txt' if n == 5 else f'results/wl{n}.txt'
    d = [tuple(map(float, l.split()[:2])) for l in open(f)]
    return np.array([x for x, _ in d]), np.array([y for _, y in d])
def cross(n, L, S, cut, deg):
    pk = int(L[np.argmax(S)]); m = (L >= pk) & (L <= cut)
    if m.sum() < deg + 2: return None
    p = np.polyfit(L[m], S[m], deg); target = n*math.log(2) + math.lgamma(n+1)
    for x in np.arange(cut, 4*cut, 0.01):
        if np.polyval(p, x) <= target: return x
    return None
reach = {5: 13, 6: 25, 7: 46, 8: 84, 9: 143}
for deg in (2, 3):
    print(f"--- polynomial degree {deg}")
    for f in (0.6, 0.7, 0.75):
        row = []
        for n in (5, 6, 7, 8):
            L, S = load(n); cut = min(int(round(f*OPT[n])), reach[n] - 1)
            x = cross(n, L, S, cut, deg)
            row.append(f"Q{n}: cut={cut} pred={x:.1f} opt={OPT[n]} ratio={x/OPT[n]:.3f}" if x else f"Q{n}: cut={cut} none")
        print(f"f={f}: " + " | ".join(row))
    L, S = load(9)
    for cut in (110, 125, 135, 142):
        x = cross(9, L, S, cut, deg); print(f"  Q9 cut={cut}: crossing={x:.1f}" if x else f"  Q9 cut={cut}: none")
