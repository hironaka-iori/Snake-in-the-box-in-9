import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 234 = true ∨ valuation q 37 = true ∨ valuation q 102 = true ∨ valuation q 106 = true ∨ valuation q 108 = true := by
  rw [value37, value102, value106, value107, value108, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(94 : Vertex), (342 : Vertex), (348 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (334 : Vertex) [(94 : Vertex), (342 : Vertex), (348 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 90 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value90, value103, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (343 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 90 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value90, value103, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (343 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 90 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value90, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (347 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value103, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (343 : Vertex) (347 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 90 = false ∨ valuation q 105 = false := by
  rw [value90, value105, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (351 : Vertex) (287 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide)

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value103, value105, value107, value108, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(343 : Vertex), (347 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (287 : Vertex) [(343 : Vertex), (347 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 90 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value90, value105, value107, value108, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(287 : Vertex), (347 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (343 : Vertex) [(287 : Vertex), (347 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 90 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value90, value103, value107, value108, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(287 : Vertex), (343 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (347 : Vertex) [(287 : Vertex), (343 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value109, value110, value111, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 236 = true ∨ valuation q 111 = true ∨ valuation q 117 = true := by
  rw [value109, value111, value117, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(386 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (385 : Vertex) [(386 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 236 = true ∨ valuation q 110 = true ∨ valuation q 117 = true := by
  rw [value109, value110, value117, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(385 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (386 : Vertex) [(385 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 236 = true ∨ valuation q 110 = true ∨ valuation q 111 = true := by
  rw [value109, value110, value111, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(385 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [(385 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value109, value110, value112, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (384 : Vertex) (389 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 237 = true ∨ valuation q 112 = true ∨ valuation q 118 = true := by
  rw [value110, value112, value118, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(389 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (384 : Vertex) [(389 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 237 = true ∨ valuation q 109 = true ∨ valuation q 118 = true := by
  rw [value109, value110, value118, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(384 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (389 : Vertex) [(384 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value109, value113, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (386 : Vertex) (384 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide)

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 238 = true ∨ valuation q 113 = true := by
  rw [value111, value113, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 238 = true ∨ valuation q 109 = true := by
  rw [value109, value111, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(384 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 40 = false ∨ valuation q 70 = false ∨ valuation q 110 = false := by
  rw [value40, value70, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 40 = false ∨ valuation q 70 = false ∨ valuation q 115 = false := by
  rw [value40, value70, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 40 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value40, value110, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 70 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value70, value110, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 70 = true ∨ valuation q 110 = true ∨ valuation q 115 = true := by
  rw [value70, value110, value112, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(261 : Vertex), (385 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (133 : Vertex) [(261 : Vertex), (385 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 40 = true ∨ valuation q 110 = true ∨ valuation q 115 = true := by
  rw [value40, value110, value112, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(133 : Vertex), (385 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (261 : Vertex) [(133 : Vertex), (385 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 40 = true ∨ valuation q 70 = true ∨ valuation q 115 = true := by
  rw [value40, value70, value112, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(133 : Vertex), (261 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (385 : Vertex) [(133 : Vertex), (261 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 40 = true ∨ valuation q 70 = true ∨ valuation q 110 = true := by
  rw [value40, value70, value110, value112, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(133 : Vertex), (261 : Vertex), (385 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (397 : Vertex) [(133 : Vertex), (261 : Vertex), (385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 45 = false ∨ valuation q 111 = false ∨ valuation q 116 = false := by
  rw [value45, value111, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 240 = true ∨ valuation q 111 = true ∨ valuation q 116 = true := by
  rw [value111, value113, value116, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(386 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (138 : Vertex) [(386 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 240 = true ∨ valuation q 45 = true ∨ valuation q 116 = true := by
  rw [value45, value113, value116, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(138 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (386 : Vertex) [(138 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 240 = true ∨ valuation q 45 = true ∨ valuation q 111 = true := by
  rw [value45, value111, value113, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(138 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (398 : Vertex) [(138 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 76 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value76, value114, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E057.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112057
