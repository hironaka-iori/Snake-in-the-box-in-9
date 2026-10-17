import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value81, value83, value85, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(342 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (346 : Vertex) [(342 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 81 = true ∨ valuation q 82 = true := by
  rw [value81, value82, value85, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 203 = true ∨ valuation q 45 = true ∨ valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 95 = true := by
  rw [value45, value86, value87, value90, value95, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(256 : Vertex), (385 : Vertex), (392 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (128 : Vertex) [(256 : Vertex), (385 : Vertex), (392 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 203 = true ∨ valuation q 15 = true ∨ valuation q 45 = true ∨ valuation q 90 = true ∨ valuation q 95 = true := by
  rw [value15, value45, value86, value90, value95, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (392 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (385 : Vertex) [(128 : Vertex), (256 : Vertex), (392 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 203 = true ∨ valuation q 15 = true ∨ valuation q 45 = true ∨ valuation q 87 = true ∨ valuation q 95 = true := by
  rw [value15, value45, value86, value87, value95, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (385 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(128 : Vertex), (256 : Vertex), (385 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 203 = true ∨ valuation q 15 = true ∨ valuation q 45 = true ∨ valuation q 87 = true ∨ valuation q 90 = true := by
  rw [value15, value45, value86, value87, value90, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (385 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [(128 : Vertex), (256 : Vertex), (385 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 46 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value46, value86, value87, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (257 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 46 = false ∨ valuation q 86 = false ∨ valuation q 96 = false := by
  rw [value46, value86, value87, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (257 : Vertex) (384 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 46 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value46, value87, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (257 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value86, value87, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (384 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 205 = true ∨ valuation q 50 = true ∨ valuation q 89 = true ∨ valuation q 99 = true := by
  rw [value50, value88, value89, value99, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(262 : Vertex), (391 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (134 : Vertex) [(262 : Vertex), (391 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 205 = true ∨ valuation q 18 = true ∨ valuation q 50 = true ∨ valuation q 99 = true := by
  rw [value18, value50, value88, value99, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(134 : Vertex), (262 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (391 : Vertex) [(134 : Vertex), (262 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 19 = false ∨ valuation q 88 = false ∨ valuation q 94 = false := by
  rw [value19, value88, value89, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (135 : Vertex) (390 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 51 = false ∨ valuation q 88 = false ∨ valuation q 94 = false := by
  rw [value51, value88, value89, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (263 : Vertex) (390 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 51 = true ∨ valuation q 88 = true ∨ valuation q 94 = true := by
  rw [value51, value88, value89, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(263 : Vertex), (390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(263 : Vertex), (390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 94 = true := by
  rw [value19, value51, value89, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(135 : Vertex), (263 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (390 : Vertex) [(135 : Vertex), (263 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 88 = true := by
  rw [value19, value51, value88, value89, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(135 : Vertex), (263 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (399 : Vertex) [(135 : Vertex), (263 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value20, value86, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (136 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 52 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value52, value86, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (264 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 208 = true ∨ valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value87, value90, value91, value92, value93, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(385 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (137 : Vertex) [(385 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 54 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value54, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (267 : Vertex) (393 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value91, value93, value94, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (399 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 211 = true ∨ valuation q 57 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value57, value92, value93, value94, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(271 : Vertex), (395 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(271 : Vertex), (395 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 211 = true ∨ valuation q 57 = true ∨ valuation q 89 = true ∨ valuation q 93 = true := by
  rw [value57, value89, value93, value94, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (395 : Vertex) → w ∈ [(271 : Vertex), (391 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (395 : Vertex) [(271 : Vertex), (391 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 211 = true ∨ valuation q 57 = true ∨ valuation q 89 = true ∨ valuation q 92 = true := by
  rw [value57, value89, value92, value94, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(271 : Vertex), (391 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (397 : Vertex) [(271 : Vertex), (391 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 86 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value86, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (384 : Vertex) (401 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 212 = true ∨ valuation q 86 = true ∨ valuation q 97 = true := by
  rw [value86, value95, value97, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(384 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (401 : Vertex) [(384 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 212 = true ∨ valuation q 86 = true ∨ valuation q 96 = true := by
  rw [value86, value95, value96, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(384 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (402 : Vertex) [(384 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value87, value95, value96, value98, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(385 : Vertex), (400 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (273 : Vertex) [(385 : Vertex), (400 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 58 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value58, value95, value96, value98, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(273 : Vertex), (400 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (385 : Vertex) [(273 : Vertex), (400 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 58 = true ∨ valuation q 87 = true ∨ valuation q 98 = true := by
  rw [value58, value87, value96, value98, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(273 : Vertex), (385 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (400 : Vertex) [(273 : Vertex), (385 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 58 = true ∨ valuation q 87 = true ∨ valuation q 95 = true := by
  rw [value58, value87, value95, value96, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(273 : Vertex), (385 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(273 : Vertex), (385 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E203.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112203
