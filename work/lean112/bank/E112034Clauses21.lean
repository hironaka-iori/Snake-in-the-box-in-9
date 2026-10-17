import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 74 = false ∨ valuation q 107 = false := by
  rw [value37, value74, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 74 = false ∨ valuation q 113 = false := by
  rw [value37, value74, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 74 = false ∨ valuation q 118 = false := by
  rw [value37, value74, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 74 = false ∨ valuation q 126 = false := by
  rw [value37, value74, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value37, value93, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (426 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 93 = false ∨ valuation q 113 = false := by
  rw [value37, value93, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 93 = false ∨ valuation q 118 = false := by
  rw [value37, value93, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (426 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 93 = false ∨ valuation q 126 = false := by
  rw [value37, value93, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (426 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value37, value107, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value37, value107, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 107 = false ∨ valuation q 126 = false := by
  rw [value37, value107, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (482 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value37, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value37, value113, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value37, value115, value118, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (494 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value74, value93, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (426 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 93 = false ∨ valuation q 113 = false := by
  rw [value74, value93, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 93 = false ∨ valuation q 118 = false := by
  rw [value74, value93, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (426 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 93 = false ∨ valuation q 126 = false := by
  rw [value74, value93, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (426 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value74, value107, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value74, value107, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 107 = false ∨ valuation q 126 = false := by
  rw [value74, value107, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (482 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value74, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value74, value113, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 74 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value74, value115, value118, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (494 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 93 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value93, value107, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 93 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value93, value107, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 93 = false ∨ valuation q 107 = false ∨ valuation q 126 = false := by
  rw [value93, value107, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (482 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 93 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value93, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 93 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value93, value113, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 93 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value93, value115, value118, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (426 : Vertex) (494 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value107, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (482 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value107, value113, value115, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (482 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E034.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112034
