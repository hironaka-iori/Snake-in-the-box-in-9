import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value64, value65, value66, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 181 = true ∨ valuation q 66 = true ∨ valuation q 74 = true := by
  rw [value64, value66, value74, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(322 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(322 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 182 = true ∨ valuation q 67 = true ∨ valuation q 69 = true := by
  rw [value65, value67, value69, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(323 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(323 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 182 = true ∨ valuation q 64 = true ∨ valuation q 69 = true := by
  rw [value64, value65, value69, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (323 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 182 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value64, value65, value67, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(320 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (329 : Vertex) [(320 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 64 = false ∨ valuation q 75 = false ∨ valuation q 101 = false := by
  rw [value64, value66, value75, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (338 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 47 = true ∨ valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 75 = true := by
  rw [value47, value64, value66, value67, value75, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(258 : Vertex), (320 : Vertex), (323 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (450 : Vertex) [(258 : Vertex), (320 : Vertex), (323 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value65, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (322 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 70 = false := by
  rw [value65, value66, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (322 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 76 = false := by
  rw [value65, value66, value67, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (322 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value65, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (327 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 76 = false := by
  rw [value65, value67, value68, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (327 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 76 = false := by
  rw [value65, value67, value70, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (321 : Vertex) (331 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value66, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (322 : Vertex) (327 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = false ∨ valuation q 68 = false ∨ valuation q 76 = false := by
  rw [value66, value67, value68, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (322 : Vertex) (327 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 76 = false := by
  rw [value67, value68, value70, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (327 : Vertex) (331 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 185 = true ∨ valuation q 73 = true ∨ valuation q 79 = true := by
  rw [value68, value73, value79, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(335 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (323 : Vertex) [(335 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 185 = true ∨ valuation q 67 = true ∨ valuation q 79 = true := by
  rw [value67, value68, value79, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(323 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(323 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 185 = true ∨ valuation q 67 = true ∨ valuation q 73 = true := by
  rw [value67, value68, value73, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(323 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (343 : Vertex) [(323 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 69 = true := by
  rw [value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (329 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 65 = false := by
  rw [value5, value51, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (265 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 70 = false := by
  rw [value5, value51, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (265 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 72 = false := by
  rw [value5, value51, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (265 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 81 = false := by
  rw [value5, value51, value69, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (265 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 105 = false := by
  rw [value5, value51, value69, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (265 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 65 = false ∨ valuation q 70 = false := by
  rw [value5, value65, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (321 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value5, value65, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 65 = false ∨ valuation q 81 = false := by
  rw [value5, value65, value69, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (321 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 65 = false ∨ valuation q 105 = false := by
  rw [value5, value65, value69, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (321 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value5, value69, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (331 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 70 = false ∨ valuation q 81 = false := by
  rw [value5, value69, value70, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (331 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 5 = false ∨ valuation q 70 = false ∨ valuation q 105 = false := by
  rw [value5, value69, value70, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (331 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E064.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112064
