import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 60 = false := by
  rw [value26, value44, value60, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (204 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 64 = false := by
  rw [value26, value44, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (204 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 65 = false := by
  rw [value26, value44, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (204 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 72 = false := by
  rw [value26, value44, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (204 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 124 = false := by
  rw [value26, value44, value63, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (204 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value26, value60, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (232 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value26, value60, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (232 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 60 = false ∨ valuation q 72 = false := by
  rw [value26, value60, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (232 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 60 = false ∨ valuation q 124 = false := by
  rw [value26, value60, value63, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (232 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value26, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (237 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value26, value63, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (237 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 26 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value26, value63, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (108 : Vertex) (238 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 44 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value44, value60, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (204 : Vertex) (232 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 44 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value44, value60, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (204 : Vertex) (232 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 44 = false ∨ valuation q 60 = false ∨ valuation q 72 = false := by
  rw [value44, value60, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (204 : Vertex) (232 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 44 = false ∨ valuation q 60 = false ∨ valuation q 124 = false := by
  rw [value44, value60, value63, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (204 : Vertex) (232 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 44 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value44, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (204 : Vertex) (237 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 44 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value44, value63, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (204 : Vertex) (237 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 44 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value44, value63, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (204 : Vertex) (238 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 60 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value60, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (232 : Vertex) (237 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 60 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value60, value63, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (232 : Vertex) (237 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 60 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value60, value63, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (232 : Vertex) (238 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value63, value64, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (237 : Vertex) (238 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 72 = false ∨ valuation q 124 = false := by
  rw [value63, value65, value72, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (236 : Vertex) (238 : Vertex) (252 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 45 = false ∨ valuation q 58 = false ∨ valuation q 63 = false := by
  rw [value45, value58, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (205 : Vertex) (229 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value58, value61, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (229 : Vertex) (233 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 45 = true ∨ valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 125 = true := by
  rw [value45, value61, value63, value64, value125, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(205 : Vertex), (233 : Vertex), (236 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (229 : Vertex) [(205 : Vertex), (233 : Vertex), (236 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 45 = true ∨ valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 63 = true := by
  rw [value45, value58, value61, value63, value64, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(205 : Vertex), (229 : Vertex), (233 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (493 : Vertex) [(205 : Vertex), (229 : Vertex), (233 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 65 = true := by
  rw [value65, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (238 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 27 = true ∨ valuation q 59 = true ∨ valuation q 63 = true := by
  rw [value27, value59, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ∈ [(110 : Vertex), (230 : Vertex), (236 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (238 : Vertex) [(110 : Vertex), (230 : Vertex), (236 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 192 = true ∨ valuation q 59 = true ∨ valuation q 63 = true := by
  rw [value59, value63, value65, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (110 : Vertex) → w ∈ [(230 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (110 : Vertex) [(230 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 192 = true ∨ valuation q 27 = true ∨ valuation q 63 = true := by
  rw [value27, value63, value65, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(110 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (230 : Vertex) [(110 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E260.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112260
