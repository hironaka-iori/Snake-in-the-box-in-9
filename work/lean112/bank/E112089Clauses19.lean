import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 61 = false ∨ valuation q 66 = false := by
  rw [value45, value61, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value45, value61, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (199 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 61 = false ∨ valuation q 115 = false := by
  rw [value45, value61, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (199 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value45, value64, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value45, value64, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (203 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value45, value64, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (203 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value45, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 66 = false ∨ valuation q 115 = false := by
  rw [value45, value66, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (205 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 67 = false ∨ valuation q 115 = false := by
  rw [value45, value67, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value61, value64, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value61, value64, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (203 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value61, value64, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (203 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value61, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 66 = false ∨ valuation q 115 = false := by
  rw [value61, value66, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 115 = false := by
  rw [value61, value67, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value64, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (203 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 115 = false := by
  rw [value64, value66, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (203 : Vertex) (205 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 115 = false := by
  rw [value64, value67, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (203 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 115 = false := by
  rw [value66, value67, value68, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (205 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 45 = true ∨ valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 115 = true := by
  rw [value45, value61, value64, value66, value67, value68, value115, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(143 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (79 : Vertex) [(143 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 27 = true ∨ valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 115 = true := by
  rw [value27, value61, value64, value66, value67, value68, value115, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(79 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (143 : Vertex) [(79 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 115 = true := by
  rw [value27, value45, value64, value66, value67, value68, value115, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(79 : Vertex), (143 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(79 : Vertex), (143 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 61 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 115 = true := by
  rw [value27, value45, value61, value66, value67, value68, value115, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(79 : Vertex), (143 : Vertex), (199 : Vertex), (205 : Vertex), (206 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (203 : Vertex) [(79 : Vertex), (143 : Vertex), (199 : Vertex), (205 : Vertex), (206 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 115 = true := by
  rw [value27, value45, value61, value64, value67, value68, value115, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(79 : Vertex), (143 : Vertex), (199 : Vertex), (203 : Vertex), (206 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [(79 : Vertex), (143 : Vertex), (199 : Vertex), (203 : Vertex), (206 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 115 = true := by
  rw [value27, value45, value61, value64, value66, value68, value115, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(79 : Vertex), (143 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (206 : Vertex) [(79 : Vertex), (143 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 67 = true := by
  rw [value27, value45, value61, value64, value66, value67, value68, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(79 : Vertex), (143 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (463 : Vertex) [(79 : Vertex), (143 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 69 = true := by
  rw [value69, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (208 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 74 = true := by
  rw [value69, value70, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ∈ [(209 : Vertex), (210 : Vertex), (216 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (208 : Vertex) [(209 : Vertex), (210 : Vertex), (216 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value69, value70, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (209 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value70, value74, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (208 : Vertex) (209 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value71, value74, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (208 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 71 = true ∨ valuation q 74 = true := by
  rw [value69, value71, value74, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(210 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (209 : Vertex) [(210 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E089.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112089
