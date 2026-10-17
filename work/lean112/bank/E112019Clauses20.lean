import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 85 = false ∨ valuation q 107 = false := by
  rw [value44, value85, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (392 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 85 = false ∨ valuation q 116 = false := by
  rw [value44, value85, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (392 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value44, value99, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 99 = false ∨ valuation q 116 = false := by
  rw [value44, value99, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (448 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 44 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value44, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 99 = false := by
  rw [value66, value85, value99, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 107 = false := by
  rw [value66, value85, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (392 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 116 = false := by
  rw [value66, value85, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (392 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value66, value99, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 99 = false ∨ valuation q 116 = false := by
  rw [value66, value99, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (448 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value66, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value85, value99, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (392 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 99 = false ∨ valuation q 116 = false := by
  rw [value85, value99, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (392 : Vertex) (448 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value85, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (392 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 99 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value99, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (448 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 67 = false ∨ valuation q 87 = false := by
  rw [value46, value67, value87, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (331 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 67 = false ∨ valuation q 102 = false := by
  rw [value46, value67, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (331 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 67 = false ∨ valuation q 110 = false := by
  rw [value46, value67, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (331 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 67 = false ∨ valuation q 118 = false := by
  rw [value46, value67, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (331 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 87 = false ∨ valuation q 102 = false := by
  rw [value46, value87, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (395 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 87 = false ∨ valuation q 110 = false := by
  rw [value46, value87, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (395 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 87 = false ∨ valuation q 118 = false := by
  rw [value46, value87, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (395 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 102 = false ∨ valuation q 110 = false := by
  rw [value46, value102, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 102 = false ∨ valuation q 118 = false := by
  rw [value46, value102, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (451 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value46, value106, value110, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 67 = false ∨ valuation q 87 = false ∨ valuation q 102 = false := by
  rw [value67, value87, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (395 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 67 = false ∨ valuation q 87 = false ∨ valuation q 110 = false := by
  rw [value67, value87, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (395 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 67 = false ∨ valuation q 87 = false ∨ valuation q 118 = false := by
  rw [value67, value87, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (395 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 110 = false := by
  rw [value67, value102, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 118 = false := by
  rw [value67, value102, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (451 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 67 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value67, value106, value110, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 87 = false ∨ valuation q 102 = false ∨ valuation q 110 = false := by
  rw [value87, value102, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E019.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112019
