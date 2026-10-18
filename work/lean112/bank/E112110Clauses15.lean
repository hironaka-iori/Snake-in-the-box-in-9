import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 86 = false ∨ valuation q 107 = false := by
  rw [value42, value86, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 86 = false ∨ valuation q 117 = false := by
  rw [value42, value86, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value42, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 104 = false ∨ valuation q 117 = false := by
  rw [value42, value104, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value42, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 86 = false ∨ valuation q 104 = false := by
  rw [value66, value86, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 86 = false ∨ valuation q 107 = false := by
  rw [value66, value86, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 86 = false ∨ valuation q 117 = false := by
  rw [value66, value86, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value66, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 104 = false ∨ valuation q 117 = false := by
  rw [value66, value104, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value66, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 86 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value86, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 86 = false ∨ valuation q 104 = false ∨ valuation q 117 = false := by
  rw [value86, value104, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 86 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value86, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 104 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value104, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (460 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value101, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (459 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 118 = false := by
  rw [value101, value103, value107, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (459 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value103, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 118 = false := by
  rw [value103, value105, value107, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value103, value105, value106, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(459 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (455 : Vertex) [(459 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value101, value105, value106, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(455 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (459 : Vertex) [(455 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value101, value103, value106, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (461 : Vertex) [(455 : Vertex), (459 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 118 = true := by
  rw [value101, value103, value105, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (462 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value101, value103, value105, value106, value107, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (479 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value96, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (465 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value96, value108, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (465 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value96, value108, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (465 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value96, value108, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value96, value108, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value96, value108, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value108, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value108, value109, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E110.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112110
