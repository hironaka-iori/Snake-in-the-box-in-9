import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 112 = false := by
  rw [value90, value92, value93, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 90 = false ∨ valuation q 103 = false ∨ valuation q 112 = false := by
  rw [value90, value93, value103, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 92 = false ∨ valuation q 103 = false ∨ valuation q 112 = false := by
  rw [value92, value93, value103, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (430 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 23 = false ∨ valuation q 58 = false ∨ valuation q 113 = false := by
  rw [value23, value58, value94, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 23 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value23, value94, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 58 = false ∨ valuation q 82 = false ∨ valuation q 95 = false := by
  rw [value58, value82, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (417 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 58 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value58, value94, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 58 = false ∨ valuation q 95 = false ∨ valuation q 113 = false := by
  rw [value58, value94, value95, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 58 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value58, value94, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 58 = false ∨ valuation q 97 = false ∨ valuation q 113 = false := by
  rw [value58, value94, value97, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (437 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 82 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value82, value94, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value94, value95, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value94, value97, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (437 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 60 = false ∨ valuation q 94 = false := by
  rw [value25, value60, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 60 = false ∨ valuation q 98 = false := by
  rw [value25, value60, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 60 = false ∨ valuation q 102 = false := by
  rw [value25, value60, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 60 = false ∨ valuation q 115 = false := by
  rw [value25, value60, value95, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value25, value94, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value25, value94, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 115 = false := by
  rw [value25, value94, value95, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value25, value95, value98, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value25, value95, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value25, value95, value102, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 60 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value60, value94, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 60 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value60, value94, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 60 = false ∨ valuation q 94 = false ∨ valuation q 115 = false := by
  rw [value60, value94, value95, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 60 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value60, value95, value98, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 60 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value60, value95, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 60 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value60, value95, value102, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value94, value95, value98, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value94, value95, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value94, value95, value102, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E026.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112026
