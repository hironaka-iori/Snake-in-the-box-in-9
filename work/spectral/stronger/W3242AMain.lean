import W3242AS00
open WinCNF WinRup
/-- The used-clause CNF `W3242A.F` of `2423_rev_s01203` (window [0, 1, 3, 7, 6, 14], alpha [3, 2, 4, 2], radius 3)
is unsatisfiable: 581 RUP steps, 29319 hints, each checked by the kernel. -/
theorem W3242A.unsatF : unsat W3242A.F :=
  fun τ hF => msat_empty (W3242A.d26855 τ (W3242A.inp_of τ hF))
