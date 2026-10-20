import W2423CS02
open WinCNF WinRup
/-- The used-clause CNF `W2423C.F` of `2423_fwd_s01234` (window [0, 1, 3, 7, 15, 31], alpha [2, 4, 2, 3], radius 3)
is unsatisfiable: 2243 RUP steps, 200503 hints, each checked by the kernel. -/
theorem W2423C.unsatF : unsat W2423C.F :=
  fun τ hF => msat_empty (W2423C.d32537 τ (W2423C.inp_of τ hF))
