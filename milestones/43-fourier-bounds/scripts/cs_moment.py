"""Second-moment (Cauchy-Schwarz / convexity) constraint on c(w) = #S-neighbours of w notin S,
combined with the singleton-square bound T >= V of the square identity.
2*D2 = sum_{w notin S} C(c(w),2) + (V-2); D2 <= ((C(n,2)-2(n-1)+3-1)V + 2(n-1) - 6)/2 from T >= V.
Exact integer arithmetic; convexity minimum with integer c split by bipartite side."""
from math import comb
def minsumC2(cnt, inc):
    # min sum C(c_i,2) over cnt nonneg integers summing to inc
    q, r = divmod(inc, cnt)
    return (cnt - r) * comb(q, 2) + r * comb(q + 1, 2)
def ok(n, V):
    N = 2 ** (n - 1)
    best = None
    # snake parity split: V_e + V_o = V, |V_e - V_o| <= 1; endpoints: if V even, endpoints on opposite sides
    for Ve in {V // 2, (V + 1) // 2}:
        Vo = V - Ve
        if Ve > N or Vo > N: continue
        # incidences into odd-side outside vertices come from even S vertices: (n-2)Ve + (#even endpoints)
        ende = 1 if V % 2 == 0 else (2 if Ve > Vo else 0)
        endo = 2 - ende
        lo = 0
        for (cnt, inc) in ((N - Vo, (n - 2) * Ve + ende), (N - Ve, (n - 2) * Vo + endo)):
            if cnt == 0:
                if inc: return False
                continue
            if inc > n * cnt: return False
            lo += minsumC2(cnt, inc)
        twoD2_lo = lo + (V - 2)
        T_coef = comb(n, 2) - 2 * (n - 1) + 3
        # T = T_coef*V + 2(n-1) - 6 - 2D2 >= V
        twoD2_hi = (T_coef - 1) * V + 2 * (n - 1) - 6
        if twoD2_lo <= twoD2_hi: return True
    return False
for n in range(5, 12):
    mv = max(V for V in range(2, 2 ** (n - 1) + 2) if ok(n, V))
    print(n, 'max V', mv, 'edges', mv - 1, 'Huang', 2 ** (n - 1) - 1)
