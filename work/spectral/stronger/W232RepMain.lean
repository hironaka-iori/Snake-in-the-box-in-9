import W232RepS00
open WinCNF WinRup
/-- The used-clause CNF `W232Rep.F` of `232_fwd_repeated` (window [0, 1, 3, 7, 6], alpha [2, 3, 2], radius 3)
is unsatisfiable: 1087 RUP steps, 50423 hints, each checked by the kernel. -/
theorem W232Rep.unsatF : unsat W232Rep.F :=
  fun τ hF => msat_empty (W232Rep.d21450 τ (W232Rep.inp_of τ hF))
