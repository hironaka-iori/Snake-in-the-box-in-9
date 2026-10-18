import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 66 = false ∨ valuation q 97 = false := by
  rw [value30, value66, value97, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 66 = false ∨ valuation q 101 = false := by
  rw [value30, value66, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 66 = false ∨ valuation q 104 = false := by
  rw [value30, value66, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 66 = false ∨ valuation q 108 = false := by
  rw [value30, value66, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 66 = false ∨ valuation q 128 = false := by
  rw [value30, value66, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value30, value97, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 97 = false ∨ valuation q 104 = false := by
  rw [value30, value97, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value30, value97, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 97 = false ∨ valuation q 128 = false := by
  rw [value30, value97, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value30, value101, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value30, value101, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 101 = false ∨ valuation q 128 = false := by
  rw [value30, value101, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (406 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value30, value104, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 104 = false ∨ valuation q 128 = false := by
  rw [value30, value104, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 30 = false ∨ valuation q 108 = false ∨ valuation q 128 = false := by
  rw [value30, value107, value108, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value66, value97, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 97 = false ∨ valuation q 104 = false := by
  rw [value66, value97, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value66, value97, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (398 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 97 = false ∨ valuation q 128 = false := by
  rw [value66, value97, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value66, value101, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value66, value101, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 128 = false := by
  rw [value66, value101, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (406 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value66, value104, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 104 = false ∨ valuation q 128 = false := by
  rw [value66, value104, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 108 = false ∨ valuation q 128 = false := by
  rw [value66, value107, value108, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value97, value101, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value97, value101, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 128 = false := by
  rw [value97, value101, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 97 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value97, value104, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 97 = false ∨ valuation q 104 = false ∨ valuation q 128 = false := by
  rw [value97, value104, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 128 = false := by
  rw [value97, value107, value108, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value101, value104, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E050.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112050
