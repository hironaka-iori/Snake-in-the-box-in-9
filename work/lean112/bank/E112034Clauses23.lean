import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 110 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value110, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (485 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 110 = false ∨ valuation q 116 = false ∨ valuation q 128 = false := by
  rw [value110, value116, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (485 : Vertex) (492 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 128 = false := by
  rw [value114, value116, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (489 : Vertex) (492 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 246 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value115, value116, value118, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(490 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (486 : Vertex) [(490 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 246 = true ∨ valuation q 111 = true ∨ valuation q 116 = true := by
  rw [value111, value116, value118, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(486 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (490 : Vertex) [(486 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 246 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value111, value115, value118, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(486 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (492 : Vertex) [(486 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 79 = false ∨ valuation q 97 = false := by
  rw [value42, value79, value97, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (369 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 79 = false ∨ valuation q 120 = false := by
  rw [value42, value79, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (369 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 79 = false ∨ valuation q 121 = false := by
  rw [value42, value79, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (369 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 79 = false ∨ valuation q 125 = false := by
  rw [value42, value79, value119, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (369 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 97 = false ∨ valuation q 120 = false := by
  rw [value42, value97, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 97 = false ∨ valuation q 121 = false := by
  rw [value42, value97, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (433 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 97 = false ∨ valuation q 125 = false := by
  rw [value42, value97, value119, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (433 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value42, value119, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (499 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 120 = false ∨ valuation q 125 = false := by
  rw [value42, value119, value120, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (499 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 42 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value42, value119, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 79 = false ∨ valuation q 97 = false ∨ valuation q 120 = false := by
  rw [value79, value97, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (369 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 79 = false ∨ valuation q 97 = false ∨ valuation q 121 = false := by
  rw [value79, value97, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (369 : Vertex) (433 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 79 = false ∨ valuation q 97 = false ∨ valuation q 125 = false := by
  rw [value79, value97, value119, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (369 : Vertex) (433 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 79 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value79, value119, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (369 : Vertex) (499 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 79 = false ∨ valuation q 120 = false ∨ valuation q 125 = false := by
  rw [value79, value119, value120, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (369 : Vertex) (499 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 79 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value79, value119, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (369 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 97 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value97, value119, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (499 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 97 = false ∨ valuation q 120 = false ∨ valuation q 125 = false := by
  rw [value97, value119, value120, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (499 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 97 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value97, value119, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value119, value120, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (499 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 80 = false ∨ valuation q 99 = false := by
  rw [value43, value80, value99, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (371 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 80 = false ∨ valuation q 108 = false := by
  rw [value43, value80, value108, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (371 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 80 = false ∨ valuation q 123 = false := by
  rw [value43, value80, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (371 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 80 = false ∨ valuation q 127 = false := by
  rw [value43, value80, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (371 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 99 = false ∨ valuation q 119 = false := by
  rw [value43, value99, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 99 = false ∨ valuation q 123 = false := by
  rw [value43, value99, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (435 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E034.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112034
