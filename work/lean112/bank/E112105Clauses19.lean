import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 107 = false := by
  rw [value48, value68, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (322 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 116 = false := by
  rw [value48, value68, value104, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (322 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value48, value85, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (386 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 85 = false ∨ valuation q 105 = false := by
  rw [value48, value85, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 85 = false ∨ valuation q 107 = false := by
  rw [value48, value85, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (386 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 85 = false ∨ valuation q 116 = false := by
  rw [value48, value85, value104, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (386 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value48, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value48, value102, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (448 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 102 = false ∨ valuation q 116 = false := by
  rw [value48, value102, value104, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (448 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value48, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value48, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 48 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value48, value104, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (454 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value68, value85, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 85 = false ∨ valuation q 105 = false := by
  rw [value68, value85, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 85 = false ∨ valuation q 107 = false := by
  rw [value68, value85, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 85 = false ∨ valuation q 116 = false := by
  rw [value68, value85, value104, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value68, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value68, value102, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (448 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 102 = false ∨ valuation q 116 = false := by
  rw [value68, value102, value104, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (448 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value68, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value68, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 68 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value68, value104, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (454 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value85, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value85, value102, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 116 = false := by
  rw [value85, value102, value104, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 85 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value85, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 85 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value85, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 85 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value85, value104, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (454 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value102, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (448 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value102, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (448 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 102 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value102, value104, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (448 : Vertex) (454 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value104, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (451 : Vertex) (454 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E105.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112105
