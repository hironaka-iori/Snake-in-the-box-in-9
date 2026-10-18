import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value73, value74, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ∈ [(343 : Vertex), (349 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (341 : Vertex) [(343 : Vertex), (349 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value74, value78, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (341 : Vertex) (343 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 78 = true := by
  rw [value73, value78, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(349 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (343 : Vertex) [(349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 74 = true := by
  rw [value73, value74, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (349 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 192 = true ∨ valuation q 73 = true := by
  rw [value73, value74, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (327 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 192 = true ∨ valuation q 66 = true := by
  rw [value66, value74, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (341 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 68 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value68, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (329 : Vertex) (347 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value77, value78, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (345 : Vertex) (347 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 193 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value75, value77, value78, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(347 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (329 : Vertex) [(347 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 193 = true ∨ valuation q 68 = true ∨ valuation q 78 = true := by
  rw [value68, value75, value78, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(329 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (347 : Vertex) [(329 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 193 = true ∨ valuation q 68 = true ∨ valuation q 77 = true := by
  rw [value68, value75, value77, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(329 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (349 : Vertex) [(329 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 77 = true := by
  rw [value69, value72, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ∈ [(330 : Vertex), (338 : Vertex), (347 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (346 : Vertex) [(330 : Vertex), (338 : Vertex), (347 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 72 = true ∨ valuation q 77 = true := by
  rw [value72, value76, value77, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(338 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (330 : Vertex) [(338 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 69 = true ∨ valuation q 77 = true := by
  rw [value69, value76, value77, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(330 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (338 : Vertex) [(330 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value69, value72, value76, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(330 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (347 : Vertex) [(330 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 76 = true := by
  rw [value76, value77, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(346 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (345 : Vertex) [(346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 75 = true := by
  rw [value75, value77, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (346 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 196 = true ∨ valuation q 75 = true := by
  rw [value75, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (341 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 196 = true ∨ valuation q 73 = true := by
  rw [value73, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (345 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 14 = false ∨ valuation q 80 = false ∨ valuation q 82 = false := by
  rw [value14, value79, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (386 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 14 = false ∨ valuation q 80 = false ∨ valuation q 85 = false := by
  rw [value14, value79, value80, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (386 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value79, value80, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 197 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 85 = true := by
  rw [value79, value80, value82, value85, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (128 : Vertex) [(386 : Vertex), (388 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 197 = true ∨ valuation q 14 = true ∨ valuation q 80 = true ∨ valuation q 82 = true := by
  rw [value14, value79, value80, value82, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(128 : Vertex), (386 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(128 : Vertex), (386 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 83 = false := by
  rw [value16, value50, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 87 = false := by
  rw [value16, value50, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 100 = false := by
  rw [value16, value50, value80, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 79 = false ∨ valuation q 83 = false := by
  rw [value16, value79, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (384 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value16, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (387 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 81 = false ∨ valuation q 87 = false := by
  rw [value16, value80, value81, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (387 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value16, value80, value81, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (387 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value16, value80, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E047.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112047
