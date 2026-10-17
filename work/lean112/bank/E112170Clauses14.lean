import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false := by
  rw [value1343]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1335 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value21, value23, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (162 : Vertex) (176 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value71, value72, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (436 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E170.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h⟩

end
end Snake9.Regrowth.E112170
