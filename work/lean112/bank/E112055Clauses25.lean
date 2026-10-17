import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 106 = true := by
  rw [value106, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (348 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = true ∨ valuation q 90 = true ∨ valuation q 97 = true ∨ valuation q 107 = true := by
  rw [value36, value90, value97, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ∈ [(92 : Vertex), (284 : Vertex), (332 : Vertex), (350 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (348 : Vertex) [(92 : Vertex), (284 : Vertex), (332 : Vertex), (350 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 90 = false ∨ valuation q 107 = false := by
  rw [value36, value90, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (92 : Vertex) (284 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value36, value97, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (92 : Vertex) (332 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 90 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value90, value97, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (284 : Vertex) (332 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 36 = false ∨ valuation q 97 = false := by
  rw [value36, value97, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (348 : Vertex) (92 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 234 = true ∨ valuation q 90 = true ∨ valuation q 97 = true ∨ valuation q 107 = true := by
  rw [value90, value97, value106, value107, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(284 : Vertex), (332 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (92 : Vertex) [(284 : Vertex), (332 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 234 = true ∨ valuation q 36 = true ∨ valuation q 97 = true ∨ valuation q 107 = true := by
  rw [value36, value97, value106, value107, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(92 : Vertex), (332 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (284 : Vertex) [(92 : Vertex), (332 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 234 = true ∨ valuation q 36 = true ∨ valuation q 90 = true ∨ valuation q 107 = true := by
  rw [value36, value90, value106, value107, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(92 : Vertex), (284 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (332 : Vertex) [(92 : Vertex), (284 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 234 = true ∨ valuation q 36 = true ∨ valuation q 90 = true ∨ valuation q 97 = true := by
  rw [value36, value90, value97, value106, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(92 : Vertex), (284 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(92 : Vertex), (284 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value37, value99, value102, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (334 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value37, value99, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (334 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 108 = false := by
  rw [value37, value99, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (334 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value37, value102, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (342 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value37, value102, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 37 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value37, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value99, value102, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (334 : Vertex) (342 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value99, value102, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (334 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 99 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value99, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (334 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value102, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 235 = true ∨ valuation q 37 = true ∨ valuation q 102 = true ∨ valuation q 106 = true ∨ valuation q 108 = true := by
  rw [value37, value102, value106, value107, value108, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(94 : Vertex), (342 : Vertex), (348 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (334 : Vertex) [(94 : Vertex), (342 : Vertex), (348 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 235 = true ∨ valuation q 37 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 108 = true := by
  rw [value37, value99, value102, value107, value108, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(94 : Vertex), (334 : Vertex), (342 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(94 : Vertex), (334 : Vertex), (342 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value91, value103, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ∈ [(287 : Vertex), (343 : Vertex), (347 : Vertex), (350 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (351 : Vertex) [(287 : Vertex), (343 : Vertex), (347 : Vertex), (350 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value91, value103, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (343 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value91, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (347 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value103, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (343 : Vertex) (347 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 91 = false ∨ valuation q 107 = false := by
  rw [value91, value107, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (351 : Vertex) (287 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide)

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value103, value107, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (351 : Vertex) (343 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide)

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value103, value105, value107, value108, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(343 : Vertex), (347 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (287 : Vertex) [(343 : Vertex), (347 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 91 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value91, value105, value107, value108, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(287 : Vertex), (347 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (343 : Vertex) [(287 : Vertex), (347 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 91 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value91, value103, value107, value108, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(287 : Vertex), (343 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (347 : Vertex) [(287 : Vertex), (343 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 91 = true ∨ valuation q 103 = true ∨ valuation q 105 = true := by
  rw [value91, value103, value105, value108, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(287 : Vertex), (343 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (350 : Vertex) [(287 : Vertex), (343 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block25 (q : Snake 81) (h : Conditions q) : B112E055.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112055
