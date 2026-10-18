import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 78 = false ∨ valuation q 119 = false := by
  rw [value53, value78, value100, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value53, value88, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 103 = false := by
  rw [value53, value88, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 106 = false := by
  rw [value53, value88, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 119 = false := by
  rw [value53, value88, value100, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value53, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value53, value100, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 101 = false ∨ valuation q 119 = false := by
  rw [value53, value100, value101, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value53, value100, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 103 = false ∨ valuation q 119 = false := by
  rw [value53, value100, value103, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (437 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 106 = false ∨ valuation q 119 = false := by
  rw [value53, value100, value106, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value78, value88, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (417 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 103 = false := by
  rw [value78, value88, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (417 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 106 = false := by
  rw [value78, value88, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (417 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 119 = false := by
  rw [value78, value88, value100, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (417 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value78, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value78, value100, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 101 = false ∨ valuation q 119 = false := by
  rw [value78, value100, value101, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value78, value100, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 103 = false ∨ valuation q 119 = false := by
  rw [value78, value100, value103, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (437 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 106 = false ∨ valuation q 119 = false := by
  rw [value78, value100, value106, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value88, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value88, value100, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 119 = false := by
  rw [value88, value100, value101, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value88, value100, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 103 = false ∨ valuation q 119 = false := by
  rw [value88, value100, value103, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (437 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 106 = false ∨ valuation q 119 = false := by
  rw [value88, value100, value106, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value100, value101, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 119 = false := by
  rw [value100, value101, value103, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 106 = false ∨ valuation q 119 = false := by
  rw [value100, value101, value106, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (435 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 119 = false := by
  rw [value100, value103, value106, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (437 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 55 = false ∨ valuation q 80 = false ∨ valuation q 121 = false := by
  rw [value55, value80, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E121.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112121
