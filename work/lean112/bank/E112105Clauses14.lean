import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 78 = true := by
  rw [value78, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (341 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 69 = true ∨ valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 118 = true := by
  rw [value69, value77, value78, value79, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ∈ [(325 : Vertex), (340 : Vertex), (343 : Vertex), (469 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (341 : Vertex) [(325 : Vertex), (340 : Vertex), (343 : Vertex), (469 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 69 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value69, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (340 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 69 = false ∨ valuation q 77 = false ∨ valuation q 118 = false := by
  rw [value69, value77, value78, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (340 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 118 = true := by
  rw [value77, value78, value79, value118, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(340 : Vertex), (343 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (325 : Vertex) [(340 : Vertex), (343 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 69 = true ∨ valuation q 79 = true ∨ valuation q 118 = true := by
  rw [value69, value78, value79, value118, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(325 : Vertex), (343 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (340 : Vertex) [(325 : Vertex), (343 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 69 = true ∨ valuation q 77 = true ∨ valuation q 118 = true := by
  rw [value69, value77, value78, value118, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(325 : Vertex), (340 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (343 : Vertex) [(325 : Vertex), (340 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 69 = true ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value69, value77, value78, value79, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(325 : Vertex), (340 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (469 : Vertex) [(325 : Vertex), (340 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value71, value76, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (339 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 71 = true ∨ valuation q 78 = true := by
  rw [value71, value78, value79, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(327 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (339 : Vertex) [(327 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 71 = true ∨ valuation q 76 = true := by
  rw [value71, value76, value79, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(327 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (341 : Vertex) [(327 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value72, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (328 : Vertex) (345 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value80, value81, value83, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (344 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(345 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (344 : Vertex) (328 : Vertex) [(345 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true ∨ valuation q 72 = true ∨ valuation q 83 = true := by
  rw [value72, value80, value83, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (344 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(328 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (344 : Vertex) (345 : Vertex) [(328 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 73 = true ∨ valuation q 80 = true ∨ valuation q 82 = true := by
  rw [value73, value80, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ∈ [(329 : Vertex), (344 : Vertex), (347 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (345 : Vertex) [(329 : Vertex), (344 : Vertex), (347 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 73 = false ∨ valuation q 80 = false ∨ valuation q 82 = false := by
  rw [value73, value80, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (329 : Vertex) (344 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 80 = true ∨ valuation q 82 = true := by
  rw [value80, value81, value82, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(344 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (329 : Vertex) [(344 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 73 = true ∨ valuation q 82 = true := by
  rw [value73, value81, value82, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(329 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (344 : Vertex) [(329 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 73 = true ∨ valuation q 80 = true := by
  rw [value73, value80, value81, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(329 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (347 : Vertex) [(329 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 81 = true := by
  rw [value81, value82, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (339 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 76 = true := by
  rw [value76, value82, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (345 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 83 = true := by
  rw [value83, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (348 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 77 = true ∨ valuation q 80 = true ∨ valuation q 121 = true := by
  rw [value77, value80, value83, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ∈ [(340 : Vertex), (344 : Vertex), (476 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (348 : Vertex) [(340 : Vertex), (344 : Vertex), (476 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 77 = false ∨ valuation q 80 = false ∨ valuation q 121 = false := by
  rw [value77, value80, value83, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (340 : Vertex) (344 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 80 = true ∨ valuation q 121 = true := by
  rw [value80, value83, value121, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(344 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (340 : Vertex) [(344 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 77 = true ∨ valuation q 121 = true := by
  rw [value77, value83, value121, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(340 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (344 : Vertex) [(340 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 77 = true ∨ valuation q 80 = true := by
  rw [value77, value80, value83, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(340 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (476 : Vertex) [(340 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 102 = false := by
  rw [value84, value85, value89, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 89 = true ∨ valuation q 102 = true := by
  rw [value84, value89, value102, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(392 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (386 : Vertex) [(392 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 85 = true ∨ valuation q 102 = true := by
  rw [value84, value85, value102, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(386 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(386 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 85 = true ∨ valuation q 89 = true := by
  rw [value84, value85, value89, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(386 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (448 : Vertex) [(386 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 85 = true := by
  rw [value85, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (386 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block14 (q : Snake 81) (h : Conditions q) : B112E105.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112105
