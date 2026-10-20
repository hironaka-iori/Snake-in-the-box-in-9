import W41cDisS01
open WinCNF WinRup
/-- The used-clause CNF `W41cDis.F` of `41c_fwd_distinct` (window [0, 1, 3, 7, 15], alpha [4, 1, [4, 6]], radius 3)
is unsatisfiable: 1600 RUP steps, 113983 hints, each checked by the kernel. -/
theorem W41cDis.unsatF : unsat W41cDis.F :=
  fun τ hF => msat_empty (W41cDis.d24314 τ (W41cDis.inp_of τ hF))
