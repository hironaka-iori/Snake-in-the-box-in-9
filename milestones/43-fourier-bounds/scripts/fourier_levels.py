"""Exact Fourier-level (Hoffman / total-influence) bounds for an induced path with V vertices.
f = 1_S, mu = V/2^n.  Edge count inside: f^T A f = 2(V-1) = 2^n sum_T fhat(T)^2 (n - 2|T|).
(H)  all levels: 2(V-1) >= n 2^n mu^2 - n 2^n (mu - mu^2)
(HP) parity-corrected: level n carries fhat([n])^2 = ((V_e-V_o)/2^n)^2 <= 1/4^n, the rest has |T| <= n-1:
     2(V-1) >= n 2^n mu^2 - (n-2) 2^n (mu - mu^2 - w_n) - n 2^n w_n,  w_n = 1/4^n.
Returns the largest V allowed (exact rationals)."""
from fractions import Fraction as F
def H(n, V):
    N = 2 ** n; mu = F(V, N)
    return 2 * (V - 1) >= n * N * mu * mu - n * N * (mu - mu * mu)
def HP(n, V):
    N = 2 ** n; mu = F(V, N); wn = F(1 if V % 2 else 0, N * N)
    return 2 * (V - 1) >= n * N * mu * mu - (n - 2) * N * (mu - mu * mu - wn) - n * N * wn
for n in (7, 8, 9):
    a = max(V for V in range(2, 2 ** n) if H(n, V)); b = max(V for V in range(2, 2 ** n) if HP(n, V))
    print(n, 'Hoffman edges', a - 1, 'parity-corrected edges', b - 1)
