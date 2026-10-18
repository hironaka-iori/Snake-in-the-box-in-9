import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value85, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value88, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (426 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 213 = true ∨ valuation q 85 = true ∨ valuation q 90 = true ∨ valuation q 92 = true := by
  rw [value85, value90, value91, value92, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(422 : Vertex), (428 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (426 : Vertex) [(422 : Vertex), (428 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 213 = true ∨ valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 92 = true := by
  rw [value85, value88, value91, value92, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(422 : Vertex), (426 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (428 : Vertex) [(422 : Vertex), (426 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 63 = false ∨ valuation q 86 = false ∨ valuation q 112 = false := by
  rw [value63, value86, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 63 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value63, value92, value102, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value86, value89, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value91, value92, value102, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (430 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 29 = false ∨ valuation q 65 = false ∨ valuation q 99 = false := by
  rw [value29, value65, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 29 = false ∨ valuation q 65 = false ∨ valuation q 114 = false := by
  rw [value29, value65, value93, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 29 = false ∨ valuation q 81 = false ∨ valuation q 99 = false := by
  rw [value29, value81, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 29 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value29, value93, value94, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 65 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value65, value93, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 65 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value65, value93, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 65 = false ∨ valuation q 99 = false ∨ valuation q 114 = false := by
  rw [value65, value93, value99, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 81 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value81, value93, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 114 = false := by
  rw [value93, value94, value96, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 99 = false ∨ valuation q 114 = false := by
  rw [value93, value94, value99, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (435 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 67 = false ∨ valuation q 93 = false := by
  rw [value31, value67, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 67 = false ∨ valuation q 97 = false := by
  rw [value31, value67, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 67 = false ∨ valuation q 101 = false := by
  rw [value31, value67, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 67 = false ∨ valuation q 116 = false := by
  rw [value31, value67, value94, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value31, value93, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value31, value93, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 93 = false ∨ valuation q 116 = false := by
  rw [value31, value93, value94, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value31, value94, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 97 = false ∨ valuation q 116 = false := by
  rw [value31, value94, value97, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 31 = false ∨ valuation q 101 = false ∨ valuation q 116 = false := by
  rw [value31, value94, value101, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 67 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value67, value93, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 67 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value67, value93, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 67 = false ∨ valuation q 93 = false ∨ valuation q 116 = false := by
  rw [value67, value93, value94, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 67 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value67, value94, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.First112
