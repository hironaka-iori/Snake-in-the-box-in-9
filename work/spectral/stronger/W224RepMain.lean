import W224RepS09
open WinCNF WinRup
/-- The used-clause CNF `W224Rep.F` of `224_fwd_repeated` (window [0, 1, 3, 7, 6], alpha [2, 2, 4], radius 3)
is unsatisfiable: 18782 RUP steps, 988759 hints, each checked by the kernel. -/
theorem W224Rep.unsatF : unsat W224Rep.F :=
  fun τ hF => msat_empty (W224Rep.d53415 τ (W224Rep.inp_of τ hF))
