import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 107 = false ∨ valuation q 123 = false := by
  rw [value74, value107, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (454 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value74, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 110 = false ∨ valuation q 123 = false := by
  rw [value74, value110, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value74, value112, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value91, value107, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (454 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value91, value107, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (454 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 107 = false ∨ valuation q 123 = false := by
  rw [value91, value107, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (454 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value91, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 110 = false ∨ valuation q 123 = false := by
  rw [value91, value110, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value91, value112, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 107 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value107, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (454 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 107 = false ∨ valuation q 110 = false ∨ valuation q 123 = false := by
  rw [value107, value110, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (454 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value107, value112, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (454 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value110, value112, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (460 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 74 = true ∨ valuation q 91 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 113 = true ∨ valuation q 123 = true := by
  rw [value74, value91, value107, value110, value112, value113, value123, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(334 : Vertex), (398 : Vertex), (454 : Vertex), (460 : Vertex), (463 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (206 : Vertex) [(334 : Vertex), (398 : Vertex), (454 : Vertex), (460 : Vertex), (463 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 56 = true ∨ valuation q 91 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 113 = true ∨ valuation q 123 = true := by
  rw [value56, value91, value107, value110, value112, value113, value123, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(206 : Vertex), (398 : Vertex), (454 : Vertex), (460 : Vertex), (463 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (334 : Vertex) [(206 : Vertex), (398 : Vertex), (454 : Vertex), (460 : Vertex), (463 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 56 = true ∨ valuation q 74 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 113 = true ∨ valuation q 123 = true := by
  rw [value56, value74, value107, value110, value112, value113, value123, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(206 : Vertex), (334 : Vertex), (454 : Vertex), (460 : Vertex), (463 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (398 : Vertex) [(206 : Vertex), (334 : Vertex), (454 : Vertex), (460 : Vertex), (463 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 56 = true ∨ valuation q 74 = true ∨ valuation q 91 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 123 = true := by
  rw [value56, value74, value91, value107, value110, value112, value123, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(206 : Vertex), (334 : Vertex), (398 : Vertex), (454 : Vertex), (460 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (463 : Vertex) [(206 : Vertex), (334 : Vertex), (398 : Vertex), (454 : Vertex), (460 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 56 = true ∨ valuation q 74 = true ∨ valuation q 91 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 113 = true := by
  rw [value56, value74, value91, value107, value110, value112, value113, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(206 : Vertex), (334 : Vertex), (398 : Vertex), (454 : Vertex), (460 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (478 : Vertex) [(206 : Vertex), (334 : Vertex), (398 : Vertex), (454 : Vertex), (460 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 57 = false ∨ valuation q 75 = false ∨ valuation q 92 = false := by
  rw [value57, value75, value92, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 57 = false ∨ valuation q 92 = false ∨ valuation q 124 = false := by
  rw [value57, value92, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (399 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 57 = false ∨ valuation q 109 = false ∨ valuation q 124 = false := by
  rw [value57, value109, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (459 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 92 = false ∨ valuation q 109 = false := by
  rw [value75, value92, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (335 : Vertex) (399 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 92 = false ∨ valuation q 111 = false := by
  rw [value75, value92, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (335 : Vertex) (399 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 92 = false ∨ valuation q 124 = false := by
  rw [value75, value92, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (335 : Vertex) (399 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value75, value109, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (335 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 109 = false ∨ valuation q 124 = false := by
  rw [value75, value109, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (335 : Vertex) (459 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value75, value111, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (335 : Vertex) (461 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 92 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value92, value109, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (399 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 92 = false ∨ valuation q 109 = false ∨ valuation q 124 = false := by
  rw [value92, value109, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (399 : Vertex) (459 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 92 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value92, value111, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (399 : Vertex) (461 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 92 = false ∨ valuation q 112 = false ∨ valuation q 124 = false := by
  rw [value92, value112, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (399 : Vertex) (462 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E105.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112105
