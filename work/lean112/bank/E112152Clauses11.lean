import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 120 = false := by
  rw [value107, value108, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (493 : Vertex) (494 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 99 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value99, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (481 : Vertex) (499 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 99 = false ∨ valuation q 112 = false ∨ valuation q 116 = false := by
  rw [value99, value110, value112, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (481 : Vertex) (499 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 99 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value99, value110, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (481 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value110, value112, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (499 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 90 = false ∨ valuation q 100 = false ∨ valuation q 112 = false := by
  rw [value90, value100, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 90 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value90, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 100 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value100, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value110, value111, value112, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(497 : Vertex), (498 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (483 : Vertex) [(497 : Vertex), (498 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 101 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value101, value111, value112, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(483 : Vertex), (498 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (497 : Vertex) [(483 : Vertex), (498 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 101 = true ∨ valuation q 110 = true ∨ valuation q 115 = true := by
  rw [value101, value110, value112, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(483 : Vertex), (497 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (498 : Vertex) [(483 : Vertex), (497 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 101 = true ∨ valuation q 110 = true ∨ valuation q 111 = true := by
  rw [value101, value110, value111, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(483 : Vertex), (497 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (503 : Vertex) [(483 : Vertex), (497 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 233 = true ∨ valuation q 71 = true ∨ valuation q 102 = true ∨ valuation q 110 = true ∨ valuation q 115 = true ∨ valuation q 118 = true := by
  rw [value71, value102, value110, value113, value115, value118, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(373 : Vertex), (485 : Vertex), (497 : Vertex), (503 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (437 : Vertex) [(373 : Vertex), (485 : Vertex), (497 : Vertex), (503 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 54 = false ∨ valuation q 93 = false ∨ valuation q 111 = false := by
  rw [value54, value93, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (246 : Vertex) (438 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 234 = true ∨ valuation q 72 = true ∨ valuation q 93 = true ∨ valuation q 103 = true ∨ valuation q 111 = true ∨ valuation q 115 = true ∨ valuation q 119 = true := by
  rw [value72, value93, value103, value111, value114, value115, value119, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(374 : Vertex), (438 : Vertex), (486 : Vertex), (498 : Vertex), (503 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (246 : Vertex) [(374 : Vertex), (438 : Vertex), (486 : Vertex), (498 : Vertex), (503 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 55 = false ∨ valuation q 73 = false ∨ valuation q 112 = false := by
  rw [value55, value73, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (247 : Vertex) (375 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 55 = false ∨ valuation q 73 = false ∨ valuation q 113 = false := by
  rw [value55, value73, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (247 : Vertex) (375 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 55 = false ∨ valuation q 73 = false ∨ valuation q 114 = false := by
  rw [value55, value73, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (247 : Vertex) (375 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 55 = false ∨ valuation q 73 = false ∨ valuation q 120 = false := by
  rw [value55, value73, value115, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (247 : Vertex) (375 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 73 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value73, value112, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (375 : Vertex) (499 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 73 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value73, value112, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (375 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 73 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value73, value112, value115, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (375 : Vertex) (499 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 73 = false ∨ valuation q 113 = false ∨ valuation q 120 = false := by
  rw [value73, value113, value115, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (375 : Vertex) (501 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 73 = false ∨ valuation q 114 = false ∨ valuation q 120 = false := by
  rw [value73, value114, value115, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (375 : Vertex) (502 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 236 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value110, value116, value118, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(497 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (249 : Vertex) [(497 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 236 = true ∨ valuation q 57 = true ∨ valuation q 118 = true := by
  rw [value57, value116, value118, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(249 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (497 : Vertex) [(249 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 236 = true ∨ valuation q 57 = true ∨ valuation q 110 = true := by
  rw [value57, value110, value116, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(249 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (509 : Vertex) [(249 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 237 = true ∨ valuation q 118 = true ∨ valuation q 119 = true := by
  rw [value117, value118, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(509 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (492 : Vertex) [(509 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 237 = true ∨ valuation q 106 = true ∨ valuation q 119 = true := by
  rw [value106, value117, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(492 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (509 : Vertex) [(492 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 237 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value106, value117, value118, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(492 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (510 : Vertex) [(492 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value107, value113, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (493 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value107, value113, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (493 : Vertex) (501 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E152.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112152
