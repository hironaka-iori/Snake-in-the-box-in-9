import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = true ∨ valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 98 = true ∨ valuation q 103 = true := by
  rw [value88, value91, value92, value93, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ∈ [(416 : Vertex), (421 : Vertex), (422 : Vertex), (428 : Vertex), (436 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (420 : Vertex) [(416 : Vertex), (421 : Vertex), (422 : Vertex), (428 : Vertex), (436 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value88, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 98 = false := by
  rw [value88, value91, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 103 = false := by
  rw [value88, value91, value92, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value88, value91, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 103 = false := by
  rw [value88, value91, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value88, value91, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value91, value92, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 103 = false := by
  rw [value91, value92, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value91, value92, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value91, value93, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 219 = true ∨ valuation q 88 = true ∨ valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value88, value91, value92, value93, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(416 : Vertex), (421 : Vertex), (422 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (428 : Vertex) [(416 : Vertex), (421 : Vertex), (422 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 35 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value35, value89, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 35 = false ∨ valuation q 89 = false ∨ valuation q 104 = false := by
  rw [value35, value89, value92, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 35 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value35, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 35 = false ∨ valuation q 91 = false ∨ valuation q 104 = false := by
  rw [value35, value91, value92, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value89, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 104 = false := by
  rw [value89, value91, value92, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 104 = true := by
  rw [value89, value91, value92, value94, value104, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (165 : Vertex) [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 35 = true ∨ valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 104 = true := by
  rw [value35, value91, value92, value94, value104, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(165 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (417 : Vertex) [(165 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 35 = true ∨ valuation q 89 = true ∨ valuation q 94 = true ∨ valuation q 104 = true := by
  rw [value35, value89, value92, value94, value104, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(165 : Vertex), (417 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (420 : Vertex) [(165 : Vertex), (417 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 35 = true ∨ valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 104 = true := by
  rw [value35, value89, value91, value92, value104, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(165 : Vertex), (417 : Vertex), (420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (423 : Vertex) [(165 : Vertex), (417 : Vertex), (420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 35 = true ∨ valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 94 = true := by
  rw [value35, value89, value91, value92, value94, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(165 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(165 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 36 = false ∨ valuation q 71 = false ∨ valuation q 91 = false := by
  rw [value36, value71, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 36 = false ∨ valuation q 71 = false ∨ valuation q 94 = false := by
  rw [value36, value71, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 71 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value71, value91, value93, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 71 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value71, value93, value94, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 71 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value71, value93, value99, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (294 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value90, value91, value93, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 90 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value90, value93, value99, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value91, value93, value99, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value93, value94, value99, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (423 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E036.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112036
