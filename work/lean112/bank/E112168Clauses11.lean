import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 187 = true ∨ valuation q 72 = true := by
  rw [value72, value73, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (327 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 68 = false ∨ valuation q 76 = false := by
  rw [value68, value76, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (337 : Vertex) (321 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 188 = true ∨ valuation q 76 = true := by
  rw [value74, value76, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 188 = true ∨ valuation q 68 = true := by
  rw [value68, value74, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value76, value77, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (338 : Vertex) (339 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 189 = true ∨ valuation q 77 = true := by
  rw [value75, value77, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (339 : Vertex) [(346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 189 = true ∨ valuation q 76 = true := by
  rw [value75, value76, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (346 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 190 = true ∨ valuation q 75 = true := by
  rw [value75, value76, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 190 = true ∨ valuation q 74 = true := by
  rw [value74, value76, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (338 : Vertex) [(337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 20 = false ∨ valuation q 75 = false ∨ valuation q 80 = false := by
  rw [value20, value75, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (90 : Vertex) (338 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 191 = true ∨ valuation q 20 = true ∨ valuation q 80 = true := by
  rw [value20, value77, value80, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(90 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (338 : Vertex) [(90 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 191 = true ∨ valuation q 20 = true ∨ valuation q 75 = true := by
  rw [value20, value75, value77, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(90 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (350 : Vertex) [(90 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 192 = true ∨ valuation q 80 = true := by
  rw [value78, value80, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (349 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 192 = true ∨ valuation q 79 = true := by
  rw [value78, value79, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(349 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 193 = true ∨ valuation q 78 = true := by
  rw [value78, value79, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (333 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 193 = true ∨ valuation q 72 = true := by
  rw [value72, value79, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (348 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value77, value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (350 : Vertex) (346 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 194 = true ∨ valuation q 78 = true := by
  rw [value78, value80, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (346 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 194 = true ∨ valuation q 77 = true := by
  rw [value77, value80, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(346 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 195 = true ∨ valuation q 82 = true := by
  rw [value81, value82, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(385 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value81, value82, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (384 : Vertex) (389 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value82, value83, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (389 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 196 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 89 = true := by
  rw [value82, value83, value86, value89, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (384 : Vertex) [(389 : Vertex), (393 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 196 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true := by
  rw [value81, value82, value83, value86, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(384 : Vertex), (389 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (401 : Vertex) [(384 : Vertex), (389 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value82, value83, value84, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 100 = false := by
  rw [value82, value83, value84, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value82, value83, value87, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value83, value84, value87, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (391 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 197 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 100 = true := by
  rw [value82, value83, value87, value100, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(385 : Vertex), (397 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (391 : Vertex) [(385 : Vertex), (397 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 198 = true ∨ valuation q 83 = true ∨ valuation q 88 = true := by
  rw [value83, value84, value88, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(389 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(389 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 198 = true ∨ valuation q 27 = true ∨ valuation q 88 = true := by
  rw [value27, value84, value88, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(135 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (389 : Vertex) [(135 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 198 = true ∨ valuation q 27 = true ∨ valuation q 83 = true := by
  rw [value27, value83, value84, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(135 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (399 : Vertex) [(135 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E168.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112168
