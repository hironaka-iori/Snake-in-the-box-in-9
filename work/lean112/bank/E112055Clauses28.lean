import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 51 = true ∨ valuation q 84 = true ∨ valuation q 122 = true ∨ valuation q 126 = true := by
  rw [value51, value84, value121, value122, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ∈ [(150 : Vertex), (278 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (406 : Vertex) [(150 : Vertex), (278 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 51 = false ∨ valuation q 84 = false ∨ valuation q 122 = false := by
  rw [value51, value84, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (150 : Vertex) (278 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 51 = false ∨ valuation q 84 = false ∨ valuation q 126 = false := by
  rw [value51, value84, value121, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (150 : Vertex) (278 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 51 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value51, value121, value122, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (150 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 84 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value84, value121, value122, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (278 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 84 = true ∨ valuation q 122 = true ∨ valuation q 126 = true := by
  rw [value84, value121, value122, value126, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(278 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (150 : Vertex) [(278 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 51 = true ∨ valuation q 122 = true ∨ valuation q 126 = true := by
  rw [value51, value121, value122, value126, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(150 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (278 : Vertex) [(150 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 51 = true ∨ valuation q 84 = true ∨ valuation q 126 = true := by
  rw [value51, value84, value121, value126, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(150 : Vertex), (278 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (407 : Vertex) [(150 : Vertex), (278 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 51 = true ∨ valuation q 84 = true ∨ valuation q 122 = true := by
  rw [value51, value84, value121, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(150 : Vertex), (278 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (414 : Vertex) [(150 : Vertex), (278 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 120 = false := by
  rw [value52, value85, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 121 = false := by
  rw [value52, value85, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 52 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value52, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 52 = false ∨ valuation q 121 = false ∨ valuation q 127 = false := by
  rw [value52, value121, value122, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 85 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value85, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 85 = false ∨ valuation q 120 = false ∨ valuation q 127 = false := by
  rw [value85, value120, value122, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (403 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 85 = false ∨ valuation q 121 = false ∨ valuation q 127 = false := by
  rw [value85, value121, value122, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 127 = false := by
  rw [value120, value121, value122, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (403 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 52 = true ∨ valuation q 85 = true ∨ valuation q 121 = true ∨ valuation q 127 = true := by
  rw [value52, value85, value121, value122, value127, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(151 : Vertex), (279 : Vertex), (406 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (403 : Vertex) [(151 : Vertex), (279 : Vertex), (406 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 123 = true := by
  rw [value123, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (409 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 87 = true ∨ valuation q 119 = true ∨ valuation q 124 = true := by
  rw [value87, value119, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ∈ [(281 : Vertex), (401 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (409 : Vertex) [(281 : Vertex), (401 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 87 = false ∨ valuation q 119 = false ∨ valuation q 124 = false := by
  rw [value87, value119, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (281 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 251 = true ∨ valuation q 119 = true ∨ valuation q 124 = true := by
  rw [value119, value123, value124, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (281 : Vertex) [(401 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 251 = true ∨ valuation q 87 = true ∨ valuation q 124 = true := by
  rw [value87, value123, value124, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(281 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(281 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 251 = true ∨ valuation q 87 = true ∨ valuation q 119 = true := by
  rw [value87, value119, value123, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(281 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(281 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 89 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value89, value120, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 89 = false ∨ valuation q 120 = false ∨ valuation q 127 = false := by
  rw [value89, value120, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (403 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 89 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value89, value123, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 120 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value120, value123, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (403 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 252 = true ∨ valuation q 120 = true ∨ valuation q 123 = true ∨ valuation q 127 = true := by
  rw [value120, value123, value124, value127, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(403 : Vertex), (409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (283 : Vertex) [(403 : Vertex), (409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 252 = true ∨ valuation q 89 = true ∨ valuation q 123 = true ∨ valuation q 127 = true := by
  rw [value89, value123, value124, value127, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(283 : Vertex), (409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (403 : Vertex) [(283 : Vertex), (409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 252 = true ∨ valuation q 89 = true ∨ valuation q 120 = true ∨ valuation q 127 = true := by
  rw [value89, value120, value124, value127, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(283 : Vertex), (403 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (409 : Vertex) [(283 : Vertex), (403 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 125 = true := by
  rw [value125, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (412 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block28 (q : Snake 81) (h : Conditions q) : B112E055.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112055
