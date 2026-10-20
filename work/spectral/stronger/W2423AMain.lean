import W2423AS00
open WinCNF WinRup
/-- The used-clause CNF `W2423A.F` of `2423_fwd_s01203` (window [0, 1, 3, 7, 6, 14], alpha [2, 4, 2, 3], radius 3)
is unsatisfiable: 867 RUP steps, 49085 hints, each checked by the kernel. -/
theorem W2423A.unsatF : unsat W2423A.F :=
  fun τ hF => msat_empty (W2423A.d26817 τ (W2423A.inp_of τ hF))
