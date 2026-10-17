import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 56 = false ∨ valuation q 97 = false ∨ valuation q 106 = false := by
  rw [value56, value87, value97, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value82, value87, value90, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 90 = false ∨ valuation q 106 = false := by
  rw [value82, value87, value90, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 97 = false ∨ valuation q 106 = false := by
  rw [value82, value87, value97, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 97 = false ∨ valuation q 106 = false := by
  rw [value87, value90, value97, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (398 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 205 = true ∨ valuation q 56 = true ∨ valuation q 82 = true ∨ valuation q 90 = true ∨ valuation q 97 = true ∨ valuation q 106 = true := by
  rw [value56, value82, value87, value90, value97, value106, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(266 : Vertex), (386 : Vertex), (398 : Vertex), (410 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (138 : Vertex) [(266 : Vertex), (386 : Vertex), (398 : Vertex), (410 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 89 = false := by
  rw [value24, value57, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 90 = false := by
  rw [value24, value57, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (268 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 98 = false := by
  rw [value24, value57, value88, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (268 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 108 = false := by
  rw [value24, value57, value88, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (268 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value24, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value24, value88, value89, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value24, value88, value89, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (397 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value24, value88, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 90 = false ∨ valuation q 108 = false := by
  rw [value24, value88, value90, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 24 = false ∨ valuation q 98 = false ∨ valuation q 108 = false := by
  rw [value24, value88, value98, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 57 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value57, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 57 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value57, value88, value89, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 57 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value57, value88, value89, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 57 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value57, value88, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 57 = false ∨ valuation q 90 = false ∨ valuation q 108 = false := by
  rw [value57, value88, value90, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 57 = false ∨ valuation q 98 = false ∨ valuation q 108 = false := by
  rw [value57, value88, value98, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value88, value89, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 108 = false := by
  rw [value88, value89, value90, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 108 = false := by
  rw [value88, value89, value98, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 108 = false := by
  rw [value88, value90, value98, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (398 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value86, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (396 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value86, value89, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (399 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 99 = true := by
  rw [value84, value88, value89, value91, value99, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(389 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (393 : Vertex) [(389 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 91 = true ∨ valuation q 99 = true := by
  rw [value84, value86, value89, value91, value99, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (399 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (396 : Vertex) [(389 : Vertex), (393 : Vertex), (399 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 99 = true := by
  rw [value84, value86, value88, value89, value99, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (396 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (399 : Vertex) [(389 : Vertex), (393 : Vertex), (396 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 91 = true := by
  rw [value84, value86, value88, value89, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(389 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E027.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112027
