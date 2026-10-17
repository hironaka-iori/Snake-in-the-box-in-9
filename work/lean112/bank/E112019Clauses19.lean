import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 222 = true ∨ valuation q 81 = true ∨ valuation q 99 = true ∨ valuation q 113 = true := by
  rw [value81, value99, value101, value113, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(386 : Vertex), (448 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(386 : Vertex), (448 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 102 = true := by
  rw [value102, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (451 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value100, value101, value102, value104, value106, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ∈ [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (451 : Vertex) [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 100 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value100, value102, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (455 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 100 = false ∨ valuation q 104 = false ∨ valuation q 114 = false := by
  rw [value100, value102, value104, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 100 = false ∨ valuation q 106 = false ∨ valuation q 114 = false := by
  rw [value100, value102, value106, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 114 = false := by
  rw [value102, value104, value106, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (455 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 101 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value101, value102, value104, value106, value114, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(450 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (449 : Vertex) [(450 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 100 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value100, value102, value104, value106, value114, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(449 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value100, value101, value102, value106, value114, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (455 : Vertex) [(449 : Vertex), (450 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 104 = true ∨ valuation q 114 = true := by
  rw [value100, value101, value102, value104, value114, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(449 : Vertex), (450 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 104 = true ∨ valuation q 106 = true := by
  rw [value100, value101, value102, value104, value106, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (467 : Vertex) [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 103 = true := by
  rw [value103, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (453 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 83 = true ∨ valuation q 100 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value83, value100, value103, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ∈ [(389 : Vertex), (449 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (453 : Vertex) [(389 : Vertex), (449 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 104 = false := by
  rw [value83, value100, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value83, value100, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 224 = true ∨ valuation q 100 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value100, value103, value104, value108, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (389 : Vertex) [(449 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 224 = true ∨ valuation q 83 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value83, value103, value104, value108, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(389 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (449 : Vertex) [(389 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 224 = true ∨ valuation q 83 = true ∨ valuation q 100 = true ∨ valuation q 108 = true := by
  rw [value83, value100, value103, value108, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(389 : Vertex), (449 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (455 : Vertex) [(389 : Vertex), (449 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 224 = true ∨ valuation q 83 = true ∨ valuation q 100 = true ∨ valuation q 104 = true := by
  rw [value83, value100, value103, value104, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(389 : Vertex), (449 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (461 : Vertex) [(389 : Vertex), (449 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 43 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value43, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 43 = false ∨ valuation q 102 = false ∨ valuation q 110 = false := by
  rw [value43, value102, value104, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 43 = false ∨ valuation q 103 = false ∨ valuation q 110 = false := by
  rw [value43, value103, value104, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 110 = false := by
  rw [value102, value103, value104, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 225 = true ∨ valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 110 = true := by
  rw [value102, value103, value104, value110, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(451 : Vertex), (453 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (199 : Vertex) [(451 : Vertex), (453 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 225 = true ∨ valuation q 43 = true ∨ valuation q 102 = true ∨ valuation q 110 = true := by
  rw [value43, value102, value104, value110, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(199 : Vertex), (451 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (453 : Vertex) [(199 : Vertex), (451 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 225 = true ∨ valuation q 43 = true ∨ valuation q 102 = true ∨ valuation q 103 = true := by
  rw [value43, value102, value103, value104, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(199 : Vertex), (451 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (463 : Vertex) [(199 : Vertex), (451 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 66 = false ∨ valuation q 85 = false := by
  rw [value44, value66, value85, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 66 = false ∨ valuation q 99 = false := by
  rw [value44, value66, value99, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 66 = false ∨ valuation q 107 = false := by
  rw [value44, value66, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 66 = false ∨ valuation q 116 = false := by
  rw [value44, value66, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 85 = false ∨ valuation q 99 = false := by
  rw [value44, value85, value99, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E019.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112019
