import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 86 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value86, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 105 = true := by
  rw [value105, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (458 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 69 = true ∨ valuation q 87 = true ∨ valuation q 100 = true ∨ valuation q 106 = true := by
  rw [value69, value87, value100, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ∈ [(330 : Vertex), (394 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (458 : Vertex) [(330 : Vertex), (394 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 69 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value69, value87, value100, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (330 : Vertex) (394 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 69 = false ∨ valuation q 87 = false ∨ valuation q 106 = false := by
  rw [value69, value87, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (330 : Vertex) (394 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 223 = true ∨ valuation q 87 = true ∨ valuation q 100 = true ∨ valuation q 106 = true := by
  rw [value87, value100, value105, value106, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(394 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (330 : Vertex) [(394 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 223 = true ∨ valuation q 69 = true ∨ valuation q 100 = true ∨ valuation q 106 = true := by
  rw [value69, value100, value105, value106, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(330 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (394 : Vertex) [(330 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 223 = true ∨ valuation q 69 = true ∨ valuation q 87 = true ∨ valuation q 106 = true := by
  rw [value69, value87, value105, value106, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(330 : Vertex), (394 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (450 : Vertex) [(330 : Vertex), (394 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 223 = true ∨ valuation q 69 = true ∨ valuation q 87 = true ∨ valuation q 100 = true := by
  rw [value69, value87, value100, value105, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(330 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (459 : Vertex) [(330 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value101, value104, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value101, value104, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value101, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (458 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value104, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value103, value104, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value104, value107, value108, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(457 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (453 : Vertex) [(457 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value106, value107, value108, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value106, value108, value118, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(459 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (461 : Vertex) [(459 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 106 = true ∨ valuation q 107 = true := by
  rw [value106, value107, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (479 : Vertex) [(459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value109, value110, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value109, value110, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value109, value110, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value109, value111, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (466 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 115 = true := by
  rw [value109, value111, value113, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(466 : Vertex), (468 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (465 : Vertex) [(466 : Vertex), (468 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value109, value110, value111, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(465 : Vertex), (466 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (468 : Vertex) [(465 : Vertex), (466 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 110 = true := by
  rw [value110, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (465 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 90 = true ∨ valuation q 109 = true ∨ valuation q 112 = true := by
  rw [value90, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ∈ [(401 : Vertex), (464 : Vertex), (467 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (465 : Vertex) [(401 : Vertex), (464 : Vertex), (467 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 90 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value90, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (401 : Vertex) (464 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 228 = true ∨ valuation q 109 = true ∨ valuation q 112 = true := by
  rw [value109, value110, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(464 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (401 : Vertex) [(464 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 228 = true ∨ valuation q 90 = true ∨ valuation q 112 = true := by
  rw [value90, value110, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(401 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (464 : Vertex) [(401 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 228 = true ∨ valuation q 90 = true ∨ valuation q 109 = true := by
  rw [value90, value109, value110, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(401 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (467 : Vertex) [(401 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 41 = false ∨ valuation q 72 = false ∨ valuation q 100 = false := by
  rw [value41, value72, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (338 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 41 = false ∨ valuation q 72 = false ∨ valuation q 109 = false := by
  rw [value41, value72, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (338 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E047.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112047
