import W223RepS02
open WinCNF WinRup
/-- The used-clause CNF `W223Rep.F` of `w223_rep` (window [0, 1, 3, 7, 6], alpha (2,2,3), radius 3)
is unsatisfiable: 1629 RUP steps, 148089 hints, each checked by the kernel. -/
theorem w223_rep_unsat : unsat W223Rep.F :=
  fun τ hF => msat_empty (W223Rep.d23240 τ (W223Rep.inp_of τ hF))
