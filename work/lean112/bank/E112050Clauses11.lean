import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 73 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value73, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (328 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 73 = false ∨ valuation q 82 = false ∨ valuation q 124 = false := by
  rw [value73, value81, value82, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (328 : Vertex) (345 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 73 = false ∨ valuation q 83 = false ∨ valuation q 124 = false := by
  rw [value73, value81, value83, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (328 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 124 = false := by
  rw [value81, value82, value83, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (345 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 84 = false := by
  rw [value76, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (337 : Vertex) (344 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 81 = true ∨ valuation q 84 = true := by
  rw [value81, value82, value84, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(344 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (337 : Vertex) [(344 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 76 = true ∨ valuation q 84 = true := by
  rw [value76, value82, value84, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(337 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (344 : Vertex) [(337 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 76 = true ∨ valuation q 81 = true := by
  rw [value76, value81, value82, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(337 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (347 : Vertex) [(337 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 74 = false ∨ valuation q 81 = false ∨ valuation q 84 = false := by
  rw [value74, value81, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (330 : Vertex) (344 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 74 = false ∨ valuation q 84 = false ∨ valuation q 125 = false := by
  rw [value74, value83, value84, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (330 : Vertex) (347 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 211 = true ∨ valuation q 74 = true ∨ valuation q 84 = true ∨ valuation q 125 = true := by
  rw [value74, value83, value84, value125, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(330 : Vertex), (347 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (344 : Vertex) [(330 : Vertex), (347 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 85 = false := by
  rw [value82, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (345 : Vertex) (346 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 67 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value67, value80, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (343 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 213 = true ∨ valuation q 80 = true ∨ valuation q 84 = true := by
  rw [value80, value84, value85, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(343 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (287 : Vertex) [(343 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 213 = true ∨ valuation q 67 = true ∨ valuation q 84 = true := by
  rw [value67, value84, value85, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(287 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (343 : Vertex) [(287 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 213 = true ∨ valuation q 67 = true ∨ valuation q 80 = true := by
  rw [value67, value80, value85, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(287 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (347 : Vertex) [(287 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 92 = false := by
  rw [value86, value87, value88, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 109 = false := by
  rw [value86, value87, value88, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 109 = false := by
  rw [value86, value87, value92, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 109 = false := by
  rw [value86, value88, value92, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (388 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 214 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 109 = true := by
  rw [value86, value87, value88, value109, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(386 : Vertex), (388 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 15 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value15, value87, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 50 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value50, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value86, value87, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 50 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value50, value86, value87, value90, value94, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (130 : Vertex) [(258 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 15 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value15, value86, value87, value90, value94, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(130 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (258 : Vertex) [(130 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 15 = true ∨ valuation q 50 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value15, value50, value87, value90, value94, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(130 : Vertex), (258 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 15 = true ∨ valuation q 50 = true ∨ valuation q 86 = true ∨ valuation q 94 = true := by
  rw [value15, value50, value86, value87, value94, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (390 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 15 = true ∨ valuation q 50 = true ∨ valuation q 86 = true ∨ valuation q 90 = true := by
  rw [value15, value50, value86, value87, value90, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 86 = false := by
  rw [value17, value52, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (260 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 99 = false := by
  rw [value17, value52, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (260 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value17, value86, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E050.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112050
