import W41cRepS00
open WinCNF WinRup
/-- The used-clause CNF `W41cRep.F` of `41c_fwd_repeated` (window [0, 1, 3, 7, 6], alpha [4, 1, [4, 6]], radius 3)
is unsatisfiable: 172 RUP steps, 6583 hints, each checked by the kernel. -/
theorem W41cRep.unsatF : unsat W41cRep.F :=
  fun τ hF => msat_empty (W41cRep.d20813 τ (W41cRep.inp_of τ hF))
