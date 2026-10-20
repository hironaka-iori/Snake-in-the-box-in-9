import W223DisS09
open WinCNF WinRup
/-- The used-clause CNF `W223Dis.F` of `w223_dis` (window [0, 1, 3, 7, 15], alpha (2,2,3), radius 3)
is unsatisfiable: 17101 RUP steps, 926950 hints, each checked by the kernel. -/
theorem w223_dis_unsat : unsat W223Dis.F :=
  fun τ hF => msat_empty (W223Dis.d45916 τ (W223Dis.inp_of τ hF))
