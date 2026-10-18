import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 12 = false ∨ valuation q 65 = false ∨ valuation q 70 = false := by
  rw [value12, value65, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (265 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 12 = false ∨ valuation q 65 = false ∨ valuation q 77 = false := by
  rw [value12, value65, value71, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (265 : Vertex) (385 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 12 = false ∨ valuation q 70 = false ∨ valuation q 77 = false := by
  rw [value12, value70, value71, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (265 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 12 = false ∨ valuation q 70 = false ∨ valuation q 86 = false := by
  rw [value12, value70, value71, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (265 : Vertex) (392 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 12 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value12, value71, value77, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (265 : Vertex) (409 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 77 = false := by
  rw [value65, value70, value71, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 86 = false := by
  rw [value65, value70, value71, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 65 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value65, value71, value77, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (409 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value70, value71, value77, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (392 : Vertex) (409 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 193 = true ∨ valuation q 12 = true ∨ valuation q 70 = true ∨ valuation q 77 = true ∨ valuation q 86 = true := by
  rw [value12, value70, value71, value77, value86, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(265 : Vertex), (392 : Vertex), (409 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (385 : Vertex) [(265 : Vertex), (392 : Vertex), (409 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value14, value67, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value14, value67, value72, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (388 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 67 = false ∨ valuation q 105 = false := by
  rw [value14, value67, value72, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (388 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 70 = false ∨ valuation q 79 = false := by
  rw [value14, value70, value72, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (392 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 70 = false ∨ valuation q 105 = false := by
  rw [value14, value70, value72, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (392 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 79 = false ∨ valuation q 105 = false := by
  rw [value14, value72, value79, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 79 = false := by
  rw [value67, value70, value72, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 105 = false := by
  rw [value67, value70, value72, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 67 = false ∨ valuation q 79 = false ∨ valuation q 105 = false := by
  rw [value67, value72, value79, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = false ∨ valuation q 79 = false ∨ valuation q 105 = false := by
  rw [value70, value72, value79, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (392 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 15 = false ∨ valuation q 69 = false ∨ valuation q 81 = false := by
  rw [value15, value69, value73, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (391 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 15 = false ∨ valuation q 69 = false := by
  rw [value15, value69, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (399 : Vertex) (271 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 15 = false ∨ valuation q 81 = false := by
  rw [value15, value81, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (399 : Vertex) (271 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 195 = true ∨ valuation q 69 = true ∨ valuation q 81 = true := by
  rw [value69, value73, value81, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(391 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (271 : Vertex) [(391 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 195 = true ∨ valuation q 15 = true ∨ valuation q 81 = true := by
  rw [value15, value73, value81, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(271 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(271 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 195 = true ∨ valuation q 15 = true ∨ valuation q 69 = true := by
  rw [value15, value69, value73, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(271 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (415 : Vertex) [(271 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 66 = true ∨ valuation q 78 = true := by
  rw [value66, value74, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ∈ [(386 : Vertex), (410 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (402 : Vertex) [(386 : Vertex), (410 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 196 = true ∨ valuation q 78 = true := by
  rw [value74, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(410 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (386 : Vertex) [(410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 196 = true ∨ valuation q 66 = true := by
  rw [value66, value74, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(386 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (410 : Vertex) [(386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 18 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value18, value67, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (276 : Vertex) (388 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 18 = false ∨ valuation q 67 = false ∨ valuation q 94 = false := by
  rw [value18, value67, value75, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (276 : Vertex) (388 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 18 = false ∨ valuation q 79 = false ∨ valuation q 94 = false := by
  rw [value18, value75, value79, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (276 : Vertex) (412 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E254.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112254
