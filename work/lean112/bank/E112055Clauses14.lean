import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 87 = true := by
  rw [value74, value75, value76, value78, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ∈ [(264 : Vertex), (267 : Vertex), (269 : Vertex), (281 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (265 : Vertex) [(264 : Vertex), (267 : Vertex), (269 : Vertex), (281 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value74, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (264 : Vertex) (267 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 87 = false := by
  rw [value75, value76, value78, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (267 : Vertex) (269 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 203 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 87 = true := by
  rw [value75, value76, value78, value87, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(267 : Vertex), (269 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (264 : Vertex) [(267 : Vertex), (269 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 203 = true ∨ valuation q 74 = true ∨ valuation q 78 = true ∨ valuation q 87 = true := by
  rw [value74, value75, value78, value87, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(264 : Vertex), (269 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (267 : Vertex) [(264 : Vertex), (269 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 203 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 87 = true := by
  rw [value74, value75, value76, value87, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(264 : Vertex), (267 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (269 : Vertex) [(264 : Vertex), (267 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 203 = true ∨ valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 78 = true := by
  rw [value74, value75, value76, value78, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(264 : Vertex), (267 : Vertex), (269 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (281 : Vertex) [(264 : Vertex), (267 : Vertex), (269 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 79 = false := by
  rw [value69, value75, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 89 = false := by
  rw [value69, value75, value76, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 69 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value69, value76, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (271 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value75, value76, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (265 : Vertex) (271 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 75 = true ∨ valuation q 79 = true ∨ valuation q 89 = true := by
  rw [value75, value76, value79, value89, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(265 : Vertex), (271 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (259 : Vertex) [(265 : Vertex), (271 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 69 = true ∨ valuation q 79 = true ∨ valuation q 89 = true := by
  rw [value69, value76, value79, value89, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(259 : Vertex), (271 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (265 : Vertex) [(259 : Vertex), (271 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 89 = true := by
  rw [value69, value75, value76, value89, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(259 : Vertex), (265 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (271 : Vertex) [(259 : Vertex), (265 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 79 = true := by
  rw [value69, value75, value76, value79, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(259 : Vertex), (265 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (283 : Vertex) [(259 : Vertex), (265 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value7, value70, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (260 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 70 = false ∨ valuation q 78 = false := by
  rw [value7, value70, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (260 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 70 = false ∨ valuation q 97 = false := by
  rw [value7, value70, value77, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (260 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value7, value74, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 74 = false ∨ valuation q 90 = false := by
  rw [value7, value74, value77, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 74 = false ∨ valuation q 97 = false := by
  rw [value7, value74, value77, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (264 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 78 = false ∨ valuation q 90 = false := by
  rw [value7, value77, value78, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (269 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 78 = false ∨ valuation q 97 = false := by
  rw [value7, value77, value78, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (269 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 78 = false ∨ valuation q 114 = false := by
  rw [value7, value77, value78, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (269 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 7 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value7, value77, value90, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value70, value74, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (264 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 90 = false := by
  rw [value70, value74, value77, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (264 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 97 = false := by
  rw [value70, value74, value77, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (264 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 70 = false ∨ valuation q 78 = false ∨ valuation q 90 = false := by
  rw [value70, value77, value78, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (269 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 70 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value70, value77, value90, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 70 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value70, value77, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (332 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value74, value77, value90, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (264 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E055.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112055
