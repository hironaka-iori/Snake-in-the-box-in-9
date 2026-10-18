import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = true ∨ valuation q 96 = true := by
  rw [value92, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ∈ [(320 : Vertex), (330 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (322 : Vertex) [(320 : Vertex), (330 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value92, value96, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (322 : Vertex) (320 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 222 = true ∨ valuation q 96 = true := by
  rw [value94, value96, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(330 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (320 : Vertex) [(330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 222 = true ∨ valuation q 92 = true := by
  rw [value92, value94, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(320 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (330 : Vertex) [(320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 23 = false ∨ valuation q 71 = false ∨ valuation q 93 = false := by
  rw [value23, value71, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (69 : Vertex) (261 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 23 = false ∨ valuation q 71 = false ∨ valuation q 98 = false := by
  rw [value23, value71, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (69 : Vertex) (261 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 23 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value23, value93, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (69 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 71 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value71, value93, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 223 = true ∨ valuation q 71 = true ∨ valuation q 93 = true ∨ valuation q 98 = true := by
  rw [value71, value93, value95, value98, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(261 : Vertex), (321 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (69 : Vertex) [(261 : Vertex), (321 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 223 = true ∨ valuation q 23 = true ∨ valuation q 71 = true ∨ valuation q 98 = true := by
  rw [value23, value71, value95, value98, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(69 : Vertex), (261 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (321 : Vertex) [(69 : Vertex), (261 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 223 = true ∨ valuation q 23 = true ∨ valuation q 71 = true ∨ valuation q 93 = true := by
  rw [value23, value71, value93, value95, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(69 : Vertex), (261 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (333 : Vertex) [(69 : Vertex), (261 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 224 = true ∨ valuation q 99 = true := by
  rw [value96, value99, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(334 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (322 : Vertex) [(334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 224 = true ∨ valuation q 94 = true := by
  rw [value94, value96, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(322 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (334 : Vertex) [(322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value77, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (333 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value77, value97, value98, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (333 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value77, value97, value99, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (334 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value97, value98, value99, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (333 : Vertex) (334 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 77 = true ∨ valuation q 99 = true ∨ valuation q 106 = true := by
  rw [value77, value97, value99, value106, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(268 : Vertex), (334 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (333 : Vertex) [(268 : Vertex), (334 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 77 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value77, value97, value98, value106, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(268 : Vertex), (333 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (334 : Vertex) [(268 : Vertex), (333 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 77 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value77, value97, value98, value99, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(268 : Vertex), (333 : Vertex), (334 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (348 : Vertex) [(268 : Vertex), (333 : Vertex), (334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 98 = true := by
  rw [value98, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (333 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = true ∨ valuation q 95 = true ∨ valuation q 97 = true := by
  rw [value78, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ∈ [(269 : Vertex), (325 : Vertex), (332 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (333 : Vertex) [(269 : Vertex), (325 : Vertex), (332 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value78, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (269 : Vertex) (325 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 95 = true ∨ valuation q 97 = true := by
  rw [value95, value97, value98, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(325 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (269 : Vertex) [(325 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 78 = true ∨ valuation q 97 = true := by
  rw [value78, value97, value98, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(269 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (325 : Vertex) [(269 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 78 = true ∨ valuation q 95 = true := by
  rw [value78, value95, value98, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(269 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (332 : Vertex) [(269 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 99 = true := by
  rw [value99, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (334 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = true ∨ valuation q 97 = true ∨ valuation q 107 = true := by
  rw [value96, value97, value99, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ∈ [(330 : Vertex), (332 : Vertex), (350 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (334 : Vertex) [(330 : Vertex), (332 : Vertex), (350 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value96, value97, value99, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (330 : Vertex) (332 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value96, value97, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (334 : Vertex) (330 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value96, value107, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (334 : Vertex) (330 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 97 = true ∨ valuation q 107 = true := by
  rw [value97, value99, value107, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(332 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (330 : Vertex) [(332 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block23 (q : Snake 81) (h : Conditions q) : B112E055.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112055
