import W223RepMain
import W223DisMain
/-! G2: the two radius-3 (2,2,3) window CNFs (used-clause parts) are unsatisfiable. -/
open WinCNF
example : unsat W223Rep.F := w223_rep_unsat
example : unsat W223Dis.F := w223_dis_unsat
example : W223Rep.F.length = 1245 ∧ W223Dis.F.length = 2172 := by decide +kernel
#print axioms w223_rep_unsat
#print axioms w223_dis_unsat
