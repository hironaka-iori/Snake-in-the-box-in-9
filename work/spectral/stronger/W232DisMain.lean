import W232DisS17
open WinCNF WinRup
/-- The used-clause CNF `W232Dis.F` of `232_fwd_distinct` (window [0, 1, 3, 7, 15], alpha [2, 3, 2], radius 3)
is unsatisfiable: 32636 RUP steps, 1756967 hints, each checked by the kernel. -/
theorem W232Dis.unsatF : unsat W232Dis.F :=
  fun τ hF => msat_empty (W232Dis.d72056 τ (W232Dis.inp_of τ hF))
