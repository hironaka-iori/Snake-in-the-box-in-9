import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 82 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value82, value102, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (392 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 96 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value96, value102, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (448 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 64 = false ∨ valuation q 84 = false := by
  rw [value40, value64, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (331 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 64 = false ∨ valuation q 99 = false := by
  rw [value40, value64, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (331 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 64 = false ∨ valuation q 107 = false := by
  rw [value40, value64, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (331 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value40, value64, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (331 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 84 = false ∨ valuation q 99 = false := by
  rw [value40, value84, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (395 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 84 = false ∨ valuation q 107 = false := by
  rw [value40, value84, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (395 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 84 = false ∨ valuation q 115 = false := by
  rw [value40, value84, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (395 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value40, value99, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 99 = false ∨ valuation q 115 = false := by
  rw [value40, value99, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (451 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value40, value103, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 84 = false ∨ valuation q 99 = false := by
  rw [value64, value84, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (395 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 84 = false ∨ valuation q 107 = false := by
  rw [value64, value84, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (395 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 84 = false ∨ valuation q 115 = false := by
  rw [value64, value84, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (395 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value64, value99, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 99 = false ∨ valuation q 115 = false := by
  rw [value64, value99, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (451 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value64, value103, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 84 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value84, value99, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 84 = false ∨ valuation q 99 = false ∨ valuation q 115 = false := by
  rw [value84, value99, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (451 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 84 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value84, value103, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 99 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value99, value103, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 221 = true ∨ valuation q 40 = true ∨ valuation q 84 = true ∨ valuation q 99 = true ∨ valuation q 107 = true ∨ valuation q 115 = true := by
  rw [value40, value84, value99, value103, value107, value115, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(203 : Vertex), (395 : Vertex), (451 : Vertex), (463 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (331 : Vertex) [(203 : Vertex), (395 : Vertex), (451 : Vertex), (463 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 41 = false ∨ valuation q 65 = false ∨ valuation q 116 = false := by
  rw [value41, value65, value104, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (332 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 41 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value41, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (461 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 100 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value100, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 223 = true ∨ valuation q 100 = true ∨ valuation q 104 = true := by
  rw [value100, value104, value105, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(453 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (463 : Vertex) [(453 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 66 = false ∨ valuation q 86 = false := by
  rw [value42, value66, value86, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 66 = false ∨ valuation q 104 = false := by
  rw [value42, value66, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 66 = false ∨ valuation q 107 = false := by
  rw [value42, value66, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 66 = false ∨ valuation q 117 = false := by
  rw [value42, value66, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 42 = false ∨ valuation q 86 = false ∨ valuation q 104 = false := by
  rw [value42, value86, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E110.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112110
