import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 70 = true ∨ valuation q 80 = true := by
  rw [value70, value78, value80, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(321 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (273 : Vertex) [(321 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 59 = true ∨ valuation q 80 = true := by
  rw [value59, value78, value80, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(273 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(273 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 59 = true ∨ valuation q 70 = true := by
  rw [value59, value70, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(273 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(273 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 196 = true ∨ valuation q 82 = true ∨ valuation q 83 = true := by
  rw [value79, value82, value83, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (339 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 196 = true ∨ valuation q 80 = true ∨ valuation q 82 = true := by
  rw [value79, value80, value82, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(339 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (346 : Vertex) [(339 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 60 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value60, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (339 : Vertex) (275 : Vertex) (337 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 197 = true ∨ valuation q 60 = true ∨ valuation q 78 = true := by
  rw [value60, value78, value80, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(275 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (338 : Vertex) [(275 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 61 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value61, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (276 : Vertex) (342 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 198 = true ∨ valuation q 82 = true ∨ valuation q 84 = true := by
  rw [value81, value82, value84, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(342 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (276 : Vertex) [(342 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 198 = true ∨ valuation q 61 = true ∨ valuation q 82 = true := by
  rw [value61, value81, value82, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(276 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (348 : Vertex) [(276 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value71, value79, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value71, value79, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 71 = false ∨ valuation q 81 = false ∨ valuation q 86 = false := by
  rw [value71, value81, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (340 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 86 = false := by
  rw [value79, value81, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (338 : Vertex) (340 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 66 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value66, value79, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (338 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value81, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (340 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 84 = true := by
  rw [value84, value85, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (333 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 76 = true := by
  rw [value76, value85, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (348 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 203 = true ∨ valuation q 82 = true ∨ valuation q 83 = true := by
  rw [value82, value83, value86, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 204 = true ∨ valuation q 46 = true ∨ valuation q 88 = true ∨ valuation q 91 = true := by
  rw [value46, value87, value88, value91, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(256 : Vertex), (385 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (128 : Vertex) [(256 : Vertex), (385 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 204 = true ∨ valuation q 16 = true ∨ valuation q 46 = true ∨ valuation q 91 = true := by
  rw [value16, value46, value87, value91, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (385 : Vertex) [(128 : Vertex), (256 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 204 = true ∨ valuation q 16 = true ∨ valuation q 46 = true ∨ valuation q 88 = true := by
  rw [value16, value46, value87, value88, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (385 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(128 : Vertex), (256 : Vertex), (385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 47 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value47, value87, value88, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (257 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 47 = false ∨ valuation q 87 = false ∨ valuation q 96 = false := by
  rw [value47, value87, value88, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (257 : Vertex) (384 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 47 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value47, value88, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (257 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value87, value88, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (384 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value92, value96, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (385 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 205 = true ∨ valuation q 47 = true ∨ valuation q 87 = true ∨ valuation q 92 = true := by
  rw [value47, value87, value88, value92, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(257 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (401 : Vertex) [(257 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 51 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value51, value89, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 51 = true ∨ valuation q 90 = true ∨ valuation q 99 = true := by
  rw [value51, value89, value90, value99, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(262 : Vertex), (391 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (134 : Vertex) [(262 : Vertex), (391 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 19 = true ∨ valuation q 90 = true ∨ valuation q 99 = true := by
  rw [value19, value89, value90, value99, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(134 : Vertex), (391 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (262 : Vertex) [(134 : Vertex), (391 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 99 = true := by
  rw [value19, value51, value89, value99, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(134 : Vertex), (262 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (391 : Vertex) [(134 : Vertex), (262 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E081.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112081
