import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 210 = true ∨ valuation q 89 = true ∨ valuation q 97 = true := by
  rw [value86, value89, value97, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(397 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (457 : Vertex) [(397 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 83 = true ∨ valuation q 90 = true ∨ valuation q 110 = true := by
  rw [value83, value87, value90, value110, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(386 : Vertex), (398 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (138 : Vertex) [(386 : Vertex), (398 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 17 = true ∨ valuation q 90 = true ∨ valuation q 110 = true := by
  rw [value17, value87, value90, value110, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(138 : Vertex), (398 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (386 : Vertex) [(138 : Vertex), (398 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 17 = true ∨ valuation q 83 = true ∨ valuation q 110 = true := by
  rw [value17, value83, value87, value110, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(138 : Vertex), (386 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (398 : Vertex) [(138 : Vertex), (386 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 17 = true ∨ valuation q 83 = true ∨ valuation q 90 = true := by
  rw [value17, value83, value87, value90, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(138 : Vertex), (386 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (458 : Vertex) [(138 : Vertex), (386 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 54 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value54, value88, value89, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 84 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value84, value88, value89, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 86 = false := by
  rw [value20, value55, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 88 = false := by
  rw [value20, value55, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 91 = false := by
  rw [value20, value55, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 99 = false := by
  rw [value20, value55, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 112 = false := by
  rw [value20, value55, value89, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value20, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (393 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value20, value86, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (393 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 86 = false ∨ valuation q 99 = false := by
  rw [value20, value86, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 86 = false ∨ valuation q 112 = false := by
  rw [value20, value86, value89, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (393 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value20, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (396 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value20, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (396 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 88 = false ∨ valuation q 112 = false := by
  rw [value20, value88, value89, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (396 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value20, value89, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (399 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 91 = false ∨ valuation q 112 = false := by
  rw [value20, value89, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (399 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 20 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value20, value89, value99, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (413 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value55, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (393 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value55, value86, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (393 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 86 = false ∨ valuation q 99 = false := by
  rw [value55, value86, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 86 = false ∨ valuation q 112 = false := by
  rw [value55, value86, value89, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (393 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value55, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (396 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value55, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (396 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 88 = false ∨ valuation q 112 = false := by
  rw [value55, value88, value89, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (396 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value55, value89, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (399 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 91 = false ∨ valuation q 112 = false := by
  rw [value55, value89, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (399 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 55 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value55, value89, value99, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (413 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E153.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112153
