import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 122 = true := by
  rw [value122, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (475 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 111 = true ∨ valuation q 121 = true := by
  rw [value111, value121, value122, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(459 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (219 : Vertex) [(459 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 44 = false ∨ valuation q 79 = false ∨ valuation q 124 = false := by
  rw [value44, value79, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (348 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 44 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value44, value116, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 79 = false ∨ valuation q 98 = false ∨ valuation q 120 = false := by
  rw [value79, value98, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (412 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 98 = false ∨ valuation q 120 = false ∨ valuation q 124 = false := by
  rw [value98, value120, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value46, value81, value100, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (350 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 113 = false := by
  rw [value46, value81, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (350 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 118 = false := by
  rw [value46, value81, value118, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (350 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 121 = false := by
  rw [value46, value81, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (350 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 123 = false := by
  rw [value46, value81, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (350 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value46, value100, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value46, value100, value118, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (414 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 100 = false ∨ valuation q 121 = false := by
  rw [value46, value100, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (414 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 100 = false ∨ valuation q 123 = false := by
  rw [value46, value100, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (414 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value46, value113, value118, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (462 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value46, value113, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (462 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value46, value113, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (462 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value46, value118, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (470 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 118 = false ∨ valuation q 123 = false := by
  rw [value46, value118, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (470 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value46, value121, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (222 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value81, value100, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value81, value100, value118, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (414 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 121 = false := by
  rw [value81, value100, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (414 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 123 = false := by
  rw [value81, value100, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (414 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value81, value113, value118, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (462 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value81, value113, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (462 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value81, value113, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (462 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value81, value118, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (470 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 118 = false ∨ valuation q 123 = false := by
  rw [value81, value118, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (470 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value81, value121, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 100 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value100, value113, value118, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (414 : Vertex) (462 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E153.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112153
