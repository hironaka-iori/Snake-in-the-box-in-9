import FastShare00.S03
open WinCNF
/-- `FastShare00.F` is unsatisfiable: 13291 RUP steps, 905775 hints, 37 kernel-checked blocks. -/
theorem FastShare00_unsat : unsat FastShare00.F :=
  fun τ hF => FastShare00.B37 τ hF False FastRup.msat_zero
