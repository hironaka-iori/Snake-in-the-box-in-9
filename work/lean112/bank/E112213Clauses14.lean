import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 21 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value21, value74, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (72 : Vertex) (320 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 21 = false ∨ valuation q 74 = false ∨ valuation q 81 = false := by
  rw [value21, value74, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (72 : Vertex) (320 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 21 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value21, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (72 : Vertex) (329 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value74, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (320 : Vertex) (329 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 21 = true ∨ valuation q 79 = true ∨ valuation q 81 = true := by
  rw [value21, value78, value79, value81, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(72 : Vertex), (329 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(72 : Vertex), (329 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 196 = true ∨ valuation q 75 = true ∨ valuation q 80 = true ∨ valuation q 88 = true := by
  rw [value75, value79, value80, value88, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(321 : Vertex), (331 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (328 : Vertex) [(321 : Vertex), (331 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 79 = false ∨ valuation q 90 = false := by
  rw [value22, value79, value80, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (75 : Vertex) (329 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 198 = true ∨ valuation q 78 = true ∨ valuation q 82 = true := by
  rw [value78, value81, value82, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(328 : Vertex), (334 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (76 : Vertex) [(328 : Vertex), (334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 198 = true ∨ valuation q 23 = true ∨ valuation q 82 = true := by
  rw [value23, value81, value82, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(76 : Vertex), (334 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (328 : Vertex) [(76 : Vertex), (334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 198 = true ∨ valuation q 23 = true ∨ valuation q 78 = true := by
  rw [value23, value78, value81, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(76 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (334 : Vertex) [(76 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 25 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value25, value76, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (78 : Vertex) (326 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 199 = true ∨ valuation q 25 = true ∨ valuation q 81 = true := by
  rw [value25, value81, value82, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(78 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (326 : Vertex) [(78 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 86 = true ∨ valuation q 89 = true := by
  rw [value83, value86, value89, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (82 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 29 = true ∨ valuation q 89 = true := by
  rw [value29, value83, value89, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(82 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (342 : Vertex) [(82 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 29 = true ∨ valuation q 86 = true := by
  rw [value29, value83, value86, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(82 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (346 : Vertex) [(82 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 201 = true ∨ valuation q 85 = true ∨ valuation q 86 = true := by
  rw [value84, value85, value86, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(341 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (84 : Vertex) [(341 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 201 = true ∨ valuation q 31 = true ∨ valuation q 86 = true := by
  rw [value31, value84, value86, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(84 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (341 : Vertex) [(84 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 84 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value84, value85, value87, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (340 : Vertex) (343 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value85, value87, value91, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(343 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (340 : Vertex) [(343 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 76 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value76, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 76 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value76, value83, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 76 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value76, value84, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (340 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value83, value84, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (338 : Vertex) (340 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 204 = true ∨ valuation q 85 = true ∨ valuation q 86 = true := by
  rw [value85, value86, value87, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(341 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (327 : Vertex) [(341 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 204 = true ∨ valuation q 77 = true ∨ valuation q 86 = true := by
  rw [value77, value86, value87, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(327 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (341 : Vertex) [(327 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 79 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value79, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (329 : Vertex) (347 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 33 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value33, value83, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (90 : Vertex) (338 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 33 = true ∨ valuation q 90 = true := by
  rw [value33, value89, value90, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(90 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (338 : Vertex) [(90 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 80 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value80, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 207 = true ∨ valuation q 34 = true ∨ valuation q 80 = true ∨ valuation q 89 = true := by
  rw [value34, value80, value89, value90, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(91 : Vertex), (331 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (345 : Vertex) [(91 : Vertex), (331 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 208 = true ∨ valuation q 88 = true := by
  rw [value88, value91, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (341 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 208 = true ∨ valuation q 85 = true := by
  rw [value85, value91, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (345 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E213.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112213
