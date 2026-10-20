import W323RepS16
open WinCNF WinRup
/-- The used-clause CNF `W323Rep.F` of `323_fwd_repeated` (window [0, 1, 3, 7, 6], alpha [3, 2, 3], radius 3)
is unsatisfiable: 29223 RUP steps, 1652675 hints, each checked by the kernel. -/
theorem W323Rep.unsatF : unsat W323Rep.F :=
  fun τ hF => msat_empty (W323Rep.d64625 τ (W323Rep.inp_of τ hF))
