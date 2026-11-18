"""Exact arithmetic of the candidate combinations (corner identity, M = 12):
  sum_{k=0}^{m} (24 alpha_k + share_k) + 840 (m+1) <= 221136,  alpha_0, alpha_m >= 4.
(i)  chain  P m <= Q sum_{j=1}^{m-1} alpha_j + C   (K7R34C7W16: P,Q,C = 89,19,678)
(ii) uniform 7-window share floor X:  sum share >= (m-8) X / 7
(iii) uniform combined 7-window floor Y: sum_{internal} (24 alpha + share) >= (m-8) Y / 7
m is impossible iff the lower bound of the left side exceeds 221136."""
from fractions import Fraction as F
def lhs(m, P=None, Q=None, C=0, X=0, Y=0, k=7):
    v = F(840 * (m + 1) + 192)
    a = F(0)
    if P: a = max(a, 24 * F(P * m - C, Q))
    a = a + F((m - k - 1) * X, k)
    a = max(a, F((m - k - 1) * Y, k))
    return v + a
def bound(**kw):
    m = 300
    while lhs(m, **kw) > 221136: m -= 1
    return m
def need(target, key, **kw):
    lo = 0
    while bound(**{**kw, key: lo}) > target: lo += 1
    return lo
if __name__ == '__main__':
    print('230 check (89/19, C=678, X=30):', bound(P=89, Q=19, C=678, X=30))
    for t in (229, 225, 222, 221, 220):
        print(t, 'needs X >=', need(t, 'X', P=89, Q=19, C=678), 'with 89/19;  uniform combined Y >=', need(t, 'Y'))
    for X in (0, 30, 60, 100, 171, 243):
        # smallest lambda (as P/19 with C scaled 678/19) giving 220
        P = 89
        while bound(P=P, Q=19, C=678, X=X) > 220: P += 1
        print(f'X={X}: 220 needs lambda >= {P}/19 = {P/19:.3f} (C=678/19)')
    for Y in (1083, 1100, 1128):
        print('Y', Y, '->', bound(Y=Y))
