import W2423BS19
open WinCNF WinRup
/-- The used-clause CNF `W2423B.F` of `2423_fwd_s01230` (window [0, 1, 3, 7, 15, 14], alpha [2, 4, 2, 3], radius 3)
is unsatisfiable: 28153 RUP steps, 1992048 hints, each checked by the kernel. -/
theorem W2423B.unsatF : unsat W2423B.F :=
  fun τ hF => msat_empty (W2423B.d73129 τ (W2423B.inp_of τ hF))
