import W323DisS44
open WinCNF WinRup
/-- The used-clause CNF `W323Dis.F` of `323_fwd_distinct` (window [0, 1, 3, 7, 15], alpha [3, 2, 3], radius 3)
is unsatisfiable: 84987 RUP steps, 4497456 hints, each checked by the kernel. -/
theorem W323Dis.unsatF : unsat W323Dis.F :=
  fun τ hF => msat_empty (W323Dis.d161760 τ (W323Dis.inp_of τ hF))
