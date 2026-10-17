import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value99, value111, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value99, value111, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value111, value112, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value111, value112, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value111, value112, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value111, value113, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (466 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 232 = true ∨ valuation q 99 = true ∨ valuation q 113 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value99, value111, value113, value115, value116, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(448 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (465 : Vertex) [(448 : Vertex), (466 : Vertex), (468 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 232 = true ∨ valuation q 99 = true ∨ valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value99, value111, value112, value113, value116, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(448 : Vertex), (465 : Vertex), (466 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (468 : Vertex) [(448 : Vertex), (465 : Vertex), (466 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 232 = true ∨ valuation q 99 = true ∨ valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 115 = true := by
  rw [value99, value111, value112, value113, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(448 : Vertex), (465 : Vertex), (466 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (472 : Vertex) [(448 : Vertex), (465 : Vertex), (466 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 112 = true := by
  rw [value112, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (465 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 100 = true ∨ valuation q 111 = true ∨ valuation q 114 = true := by
  rw [value100, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ∈ [(449 : Vertex), (464 : Vertex), (467 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (465 : Vertex) [(449 : Vertex), (464 : Vertex), (467 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 233 = true ∨ valuation q 111 = true ∨ valuation q 114 = true := by
  rw [value111, value112, value114, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(464 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (449 : Vertex) [(464 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 233 = true ∨ valuation q 100 = true ∨ valuation q 114 = true := by
  rw [value100, value112, value114, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(449 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (464 : Vertex) [(449 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 233 = true ∨ valuation q 100 = true ∨ valuation q 111 = true := by
  rw [value100, value111, value112, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(449 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (467 : Vertex) [(449 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 49 = false ∨ valuation q 70 = false ∨ valuation q 114 = false := by
  rw [value49, value70, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (338 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 49 = false ∨ valuation q 90 = false ∨ valuation q 111 = false := by
  rw [value49, value90, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (402 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 49 = false ∨ valuation q 90 = false ∨ valuation q 114 = false := by
  rw [value49, value90, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (402 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 49 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value49, value101, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (450 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 49 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value49, value111, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 70 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value70, value111, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (338 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 70 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value70, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (338 : Vertex) (467 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value90, value101, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (402 : Vertex) (450 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value90, value111, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (402 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value90, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (402 : Vertex) (467 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 234 = true ∨ valuation q 70 = true ∨ valuation q 90 = true ∨ valuation q 101 = true ∨ valuation q 111 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value70, value90, value101, value111, value113, value114, value117, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(338 : Vertex), (402 : Vertex), (450 : Vertex), (464 : Vertex), (467 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (210 : Vertex) [(338 : Vertex), (402 : Vertex), (450 : Vertex), (464 : Vertex), (467 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 234 = true ∨ valuation q 49 = true ∨ valuation q 70 = true ∨ valuation q 101 = true ∨ valuation q 111 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value49, value70, value101, value111, value113, value114, value117, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(210 : Vertex), (338 : Vertex), (450 : Vertex), (464 : Vertex), (467 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (402 : Vertex) [(210 : Vertex), (338 : Vertex), (450 : Vertex), (464 : Vertex), (467 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 102 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value102, value112, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (465 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 102 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value102, value112, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (465 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 102 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value102, value113, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (466 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value112, value113, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (465 : Vertex) (466 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 235 = true ∨ valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 118 = true := by
  rw [value112, value113, value114, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(465 : Vertex), (466 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (451 : Vertex) [(465 : Vertex), (466 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 235 = true ∨ valuation q 102 = true ∨ valuation q 113 = true ∨ valuation q 118 = true := by
  rw [value102, value113, value114, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(451 : Vertex), (466 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (465 : Vertex) [(451 : Vertex), (466 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block23 (q : Snake 81) (h : Conditions q) : B112E019.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112019
