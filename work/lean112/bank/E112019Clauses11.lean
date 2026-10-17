import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value66, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (328 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 116 = false := by
  rw [value66, value74, value75, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (328 : Vertex) (345 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 66 = false ∨ valuation q 76 = false ∨ valuation q 116 = false := by
  rw [value66, value74, value76, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (328 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 116 = false := by
  rw [value74, value75, value76, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (345 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value74, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ∈ [(344 : Vertex), (347 : Vertex), (349 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (345 : Vertex) [(344 : Vertex), (347 : Vertex), (349 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value74, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (344 : Vertex) (347 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value74, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (345 : Vertex) (344 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value77, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (345 : Vertex) (347 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 196 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value75, value77, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(347 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (344 : Vertex) [(347 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 196 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value74, value75, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(344 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (347 : Vertex) [(344 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 196 = true ∨ valuation q 74 = true ∨ valuation q 77 = true := by
  rw [value74, value75, value77, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(344 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (349 : Vertex) [(344 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value59, value70, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (338 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 70 = false ∨ valuation q 77 = false := by
  rw [value59, value70, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (338 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 70 = false ∨ valuation q 117 = false := by
  rw [value59, value70, value76, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (338 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value59, value74, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (344 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 74 = false ∨ valuation q 117 = false := by
  rw [value59, value74, value76, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (344 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 59 = false ∨ valuation q 77 = false ∨ valuation q 117 = false := by
  rw [value59, value76, value77, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (347 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 117 = false := by
  rw [value70, value74, value76, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (338 : Vertex) (344 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 70 = false ∨ valuation q 77 = false ∨ valuation q 117 = false := by
  rw [value70, value76, value77, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (338 : Vertex) (347 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 197 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 77 = true ∨ valuation q 117 = true := by
  rw [value70, value74, value76, value77, value117, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(338 : Vertex), (344 : Vertex), (347 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (282 : Vertex) [(338 : Vertex), (344 : Vertex), (347 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 197 = true ∨ valuation q 59 = true ∨ valuation q 74 = true ∨ valuation q 77 = true ∨ valuation q 117 = true := by
  rw [value59, value74, value76, value77, value117, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(282 : Vertex), (344 : Vertex), (347 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (338 : Vertex) [(282 : Vertex), (344 : Vertex), (347 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 197 = true ∨ valuation q 59 = true ∨ valuation q 70 = true ∨ valuation q 77 = true ∨ valuation q 117 = true := by
  rw [value59, value70, value76, value77, value117, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(282 : Vertex), (338 : Vertex), (347 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (344 : Vertex) [(282 : Vertex), (338 : Vertex), (347 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 197 = true ∨ valuation q 59 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 117 = true := by
  rw [value59, value70, value74, value76, value117, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(282 : Vertex), (338 : Vertex), (344 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (347 : Vertex) [(282 : Vertex), (338 : Vertex), (344 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 197 = true ∨ valuation q 59 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 77 = true := by
  rw [value59, value70, value74, value76, value77, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(282 : Vertex), (338 : Vertex), (344 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (474 : Vertex) [(282 : Vertex), (338 : Vertex), (344 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 67 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value67, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 67 = false ∨ valuation q 75 = false ∨ valuation q 118 = false := by
  rw [value67, value75, value77, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (345 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 67 = false ∨ valuation q 76 = false ∨ valuation q 118 = false := by
  rw [value67, value76, value77, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (346 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 118 = false := by
  rw [value75, value76, value77, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (345 : Vertex) (346 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 198 = true ∨ valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 118 = true := by
  rw [value75, value76, value77, value118, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(345 : Vertex), (346 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (331 : Vertex) [(345 : Vertex), (346 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 198 = true ∨ valuation q 67 = true ∨ valuation q 76 = true ∨ valuation q 118 = true := by
  rw [value67, value76, value77, value118, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(331 : Vertex), (346 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (345 : Vertex) [(331 : Vertex), (346 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 199 = true ∨ valuation q 75 = true := by
  rw [value75, value78, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (341 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 199 = true ∨ valuation q 71 = true := by
  rw [value71, value78, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (345 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E019.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112019
