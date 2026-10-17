import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 62 = false ∨ valuation q 69 = false := by
  rw [value45, value49, value62, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (296 : Vertex) (352 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value47, value48, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (294 : Vertex) (295 : Vertex) (358 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 68 = false ∨ valuation q 74 = false := by
  rw [value48, value53, value68, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (295 : Vertex) (303 : Vertex) (359 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value51, value53, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (299 : Vertex) (303 : Vertex) (363 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 69 = false ∨ valuation q 100 = false ∨ valuation q 104 = false := by
  rw [value62, value69, value100, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (352 : Vertex) (360 : Vertex) (480 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value65, value66, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (356 : Vertex) (357 : Vertex) (372 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value65, value67, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (356 : Vertex) (358 : Vertex) (364 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value69, value70, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (360 : Vertex) (362 : Vertex) (364 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value75, value76, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (369 : Vertex) (371 : Vertex) (373 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 99 = false := by
  rw [value93, value95, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (402 : Vertex) (406 : Vertex) (410 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E058.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h⟩

end
end Snake9.Regrowth.E112058
