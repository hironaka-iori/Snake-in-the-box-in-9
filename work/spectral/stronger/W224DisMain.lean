import W224DisS16
open WinCNF WinRup
/-- The used-clause CNF `W224Dis.F` of `224_fwd_distinct` (window [0, 1, 3, 7, 15], alpha [2, 2, 4], radius 3)
is unsatisfiable: 29031 RUP steps, 1682913 hints, each checked by the kernel. -/
theorem W224Dis.unsatF : unsat W224Dis.F :=
  fun τ hF => msat_empty (W224Dis.d63088 τ (W224Dis.inp_of τ hF))
