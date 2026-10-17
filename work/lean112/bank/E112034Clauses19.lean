import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 117 = false := by
  rw [value109, value110, value112, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (484 : Vertex) (487 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 121 = false := by
  rw [value109, value110, value112, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (484 : Vertex) (487 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value109, value110, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (484 : Vertex) (493 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value110, value112, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (487 : Vertex) (493 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 238 = true ∨ valuation q 35 = true ∨ valuation q 72 = true ∨ valuation q 109 = true ∨ valuation q 112 = true ∨ valuation q 117 = true := by
  rw [value35, value72, value109, value110, value112, value117, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(229 : Vertex), (357 : Vertex), (484 : Vertex), (487 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (485 : Vertex) (501 : Vertex) [(229 : Vertex), (357 : Vertex), (484 : Vertex), (487 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 111 = true := by
  rw [value111, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (486 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 112 = true ∨ valuation q 118 = true ∨ valuation q 122 = true := by
  rw [value107, value109, value111, value112, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ∈ [(482 : Vertex), (484 : Vertex), (487 : Vertex), (494 : Vertex), (502 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (486 : Vertex) [(482 : Vertex), (484 : Vertex), (487 : Vertex), (494 : Vertex), (502 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value107, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (484 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value107, value109, value111, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (484 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 122 = false := by
  rw [value107, value109, value111, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (484 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 107 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value107, value111, value112, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (487 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 107 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value107, value111, value112, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 107 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value107, value111, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (494 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value109, value111, value112, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (484 : Vertex) (487 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value109, value111, value112, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (484 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value109, value111, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (484 : Vertex) (494 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value111, value112, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (487 : Vertex) (494 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value109, value112, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (486 : Vertex) (484 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 109 = false ∨ valuation q 122 = false := by
  rw [value109, value122, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (486 : Vertex) (484 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 118 = true ∨ valuation q 122 = true := by
  rw [value107, value109, value111, value118, value122, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(482 : Vertex), (484 : Vertex), (494 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (487 : Vertex) [(482 : Vertex), (484 : Vertex), (494 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 112 = true ∨ valuation q 122 = true := by
  rw [value107, value109, value111, value112, value122, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(482 : Vertex), (484 : Vertex), (487 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (494 : Vertex) [(482 : Vertex), (484 : Vertex), (487 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 112 = true ∨ valuation q 118 = true := by
  rw [value107, value109, value111, value112, value118, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(482 : Vertex), (484 : Vertex), (487 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (502 : Vertex) [(482 : Vertex), (484 : Vertex), (487 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value91, value108, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (483 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value91, value108, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (483 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value91, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (485 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 110 = false ∨ valuation q 123 = false := by
  rw [value91, value110, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (485 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 111 = false ∨ valuation q 123 = false := by
  rw [value91, value111, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value108, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (483 : Vertex) (485 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 108 = false ∨ valuation q 111 = false ∨ valuation q 123 = false := by
  rw [value108, value111, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (483 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 123 = true := by
  rw [value108, value110, value111, value112, value123, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(483 : Vertex), (485 : Vertex), (486 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (423 : Vertex) [(483 : Vertex), (485 : Vertex), (486 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 91 = true ∨ valuation q 108 = true ∨ valuation q 111 = true ∨ valuation q 123 = true := by
  rw [value91, value108, value111, value112, value123, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(423 : Vertex), (483 : Vertex), (486 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (485 : Vertex) [(423 : Vertex), (483 : Vertex), (486 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 91 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 123 = true := by
  rw [value91, value108, value110, value112, value123, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(423 : Vertex), (483 : Vertex), (485 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(423 : Vertex), (483 : Vertex), (485 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E034.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112034
