import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 192 = true ∨ valuation q 62 = true ∨ valuation q 74 = true := by
  rw [value62, value73, value74, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(264 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(264 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 6 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value6, value70, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 6 = false ∨ valuation q 70 = false ∨ valuation q 75 = false := by
  rw [value6, value70, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 6 = false ∨ valuation q 70 = false ∨ valuation q 106 = false := by
  rw [value6, value70, value74, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (321 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 6 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value6, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 6 = false ∨ valuation q 73 = false ∨ valuation q 106 = false := by
  rw [value6, value73, value74, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (328 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 83 = false := by
  rw [value74, value75, value76, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 194 = true ∨ valuation q 74 = true ∨ valuation q 83 = true := by
  rw [value74, value75, value83, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(329 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (335 : Vertex) [(329 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 195 = true ∨ valuation q 75 = true := by
  rw [value75, value76, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (327 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 196 = true ∨ valuation q 70 = true := by
  rw [value70, value77, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value78, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (339 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 197 = true ∨ valuation q 80 = true ∨ valuation q 81 = true := by
  rw [value78, value80, value81, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (339 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 198 = true ∨ valuation q 78 = true := by
  rw [value78, value79, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 198 = true ∨ valuation q 77 = true := by
  rw [value77, value79, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (338 : Vertex) [(337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 16 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value16, value78, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (90 : Vertex) (338 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 201 = true ∨ valuation q 84 = true := by
  rw [value82, value84, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (349 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 201 = true ∨ valuation q 83 = true := by
  rw [value82, value83, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(349 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 202 = true ∨ valuation q 82 = true := by
  rw [value82, value83, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (333 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value80, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (346 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 204 = true ∨ valuation q 90 = true := by
  rw [value85, value90, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(392 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (385 : Vertex) [(392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 204 = true ∨ valuation q 86 = true := by
  rw [value85, value86, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(385 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value85, value86, value87, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (384 : Vertex) (389 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value86, value87, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (389 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 205 = true ∨ valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value85, value86, value87, value91, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(384 : Vertex), (389 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (401 : Vertex) [(384 : Vertex), (389 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value86, value87, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 105 = false := by
  rw [value86, value87, value89, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 92 = false ∨ valuation q 105 = false := by
  rw [value86, value87, value92, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 105 = false := by
  rw [value87, value89, value92, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (391 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 22 = false ∨ valuation q 61 = false ∨ valuation q 89 = false := by
  rw [value22, value61, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (262 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 22 = false ∨ valuation q 61 = false ∨ valuation q 97 = false := by
  rw [value22, value61, value88, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (262 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 208 = true ∨ valuation q 23 = true ∨ valuation q 88 = true ∨ valuation q 93 = true := by
  rw [value23, value88, value89, value93, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(135 : Vertex), (390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (389 : Vertex) [(135 : Vertex), (390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 208 = true ∨ valuation q 23 = true ∨ valuation q 87 = true ∨ valuation q 88 = true := by
  rw [value23, value87, value88, value89, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(135 : Vertex), (389 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (399 : Vertex) [(135 : Vertex), (389 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block13 (q : Snake 81) (h : Conditions q) : B112E078.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112078
