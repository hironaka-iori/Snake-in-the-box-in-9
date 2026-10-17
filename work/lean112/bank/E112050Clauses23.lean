import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 91 = false ∨ valuation q 111 = false := by
  rw [value72, value91, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value72, value91, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 91 = false ∨ valuation q 119 = false := by
  rw [value72, value91, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 91 = false ∨ valuation q 123 = false := by
  rw [value72, value91, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value72, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value72, value111, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 111 = false ∨ valuation q 123 = false := by
  rw [value72, value111, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value72, value113, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value72, value113, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (453 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 72 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value72, value114, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 91 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value91, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 91 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value91, value111, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 91 = false ∨ valuation q 111 = false ∨ valuation q 123 = false := by
  rw [value91, value111, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 91 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value91, value113, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 91 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value91, value113, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (453 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 91 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value91, value114, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value111, value113, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value111, value113, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (453 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 111 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value111, value114, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 113 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value113, value114, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (453 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 93 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value93, value110, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 93 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value93, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 110 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value110, value115, value116, value117, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(449 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (393 : Vertex) [(449 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 93 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value93, value115, value116, value117, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(393 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (449 : Vertex) [(393 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 93 = true ∨ valuation q 110 = true ∨ valuation q 117 = true := by
  rw [value93, value110, value115, value117, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(393 : Vertex), (449 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (459 : Vertex) [(393 : Vertex), (449 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 93 = true ∨ valuation q 110 = true ∨ valuation q 116 = true := by
  rw [value93, value110, value115, value116, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(393 : Vertex), (449 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (461 : Vertex) [(393 : Vertex), (449 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value95, value111, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value95, value111, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value95, value115, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 111 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value111, value115, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 244 = true ∨ valuation q 95 = true ∨ valuation q 115 = true ∨ valuation q 119 = true := by
  rw [value95, value115, value116, value119, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(395 : Vertex), (457 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (451 : Vertex) [(395 : Vertex), (457 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 244 = true ∨ valuation q 95 = true ∨ valuation q 111 = true ∨ valuation q 119 = true := by
  rw [value95, value111, value116, value119, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(395 : Vertex), (451 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (457 : Vertex) [(395 : Vertex), (451 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block23 (q : Snake 81) (h : Conditions q) : B112E050.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112050
