import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = true ∨ valuation q 83 = true := by
  rw [value71, value72, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ∈ [(333 : Vertex), (348 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (332 : Vertex) [(333 : Vertex), (348 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 72 = false ∨ valuation q 83 = false := by
  rw [value72, value83, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (332 : Vertex) (333 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 188 = true ∨ valuation q 83 = true := by
  rw [value71, value83, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (333 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 188 = true ∨ valuation q 72 = true := by
  rw [value71, value72, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (348 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 69 = false ∨ valuation q 73 = false ∨ valuation q 84 = false := by
  rw [value69, value72, value73, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 84 = true := by
  rw [value71, value72, value73, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(332 : Vertex), (335 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (329 : Vertex) [(332 : Vertex), (335 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 69 = true ∨ valuation q 73 = true ∨ valuation q 84 = true := by
  rw [value69, value72, value73, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(329 : Vertex), (335 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (332 : Vertex) [(329 : Vertex), (335 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 84 = true := by
  rw [value69, value71, value72, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(329 : Vertex), (332 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (335 : Vertex) [(329 : Vertex), (332 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 73 = true := by
  rw [value69, value71, value72, value73, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(329 : Vertex), (332 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(329 : Vertex), (332 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value68, value70, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (327 : Vertex) (331 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 86 = false := by
  rw [value68, value70, value73, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (327 : Vertex) (331 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 86 = false := by
  rw [value68, value72, value73, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (327 : Vertex) (333 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 86 = false := by
  rw [value70, value72, value73, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (331 : Vertex) (333 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 72 = false ∨ valuation q 86 = false := by
  rw [value72, value86, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (335 : Vertex) (333 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 190 = true ∨ valuation q 70 = true ∨ valuation q 72 = true ∨ valuation q 86 = true := by
  rw [value70, value72, value73, value86, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(331 : Vertex), (333 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (327 : Vertex) [(331 : Vertex), (333 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 190 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 86 = true := by
  rw [value68, value70, value73, value86, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(327 : Vertex), (331 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(327 : Vertex), (331 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 55 = false ∨ valuation q 64 = false := by
  rw [value9, value55, value64, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (272 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 55 = false ∨ valuation q 75 = false := by
  rw [value9, value55, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (272 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 55 = false ∨ valuation q 77 = false := by
  rw [value9, value55, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (272 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 55 = false ∨ valuation q 109 = false := by
  rw [value9, value55, value74, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (272 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 64 = false ∨ valuation q 80 = false := by
  rw [value9, value64, value74, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (320 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 64 = false ∨ valuation q 109 = false := by
  rw [value9, value64, value74, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (320 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 75 = false ∨ valuation q 80 = false := by
  rw [value9, value74, value75, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (338 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 75 = false ∨ valuation q 109 = false := by
  rw [value9, value74, value75, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (338 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value9, value74, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (340 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 9 = false ∨ valuation q 77 = false ∨ valuation q 109 = false := by
  rw [value9, value74, value77, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (340 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 55 = false ∨ valuation q 64 = false ∨ valuation q 75 = false := by
  rw [value55, value64, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (320 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 55 = false ∨ valuation q 64 = false ∨ valuation q 77 = false := by
  rw [value55, value64, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (320 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 55 = false ∨ valuation q 64 = false ∨ valuation q 109 = false := by
  rw [value55, value64, value74, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (320 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 55 = false ∨ valuation q 75 = false ∨ valuation q 109 = false := by
  rw [value55, value74, value75, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (338 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 55 = false ∨ valuation q 77 = false ∨ valuation q 109 = false := by
  rw [value55, value74, value77, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (272 : Vertex) (340 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 64 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value64, value74, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (320 : Vertex) (340 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E064.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112064
