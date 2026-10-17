import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value30, value96, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 96 = false ∨ valuation q 103 = false := by
  rw [value30, value96, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value30, value96, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 96 = false ∨ valuation q 127 = false := by
  rw [value30, value96, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value30, value100, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value30, value100, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 100 = false ∨ valuation q 127 = false := by
  rw [value30, value100, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (406 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value30, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 103 = false ∨ valuation q 127 = false := by
  rw [value30, value103, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 107 = false ∨ valuation q 127 = false := by
  rw [value30, value106, value107, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value65, value96, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 96 = false ∨ valuation q 103 = false := by
  rw [value65, value96, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value65, value96, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (398 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 96 = false ∨ valuation q 127 = false := by
  rw [value65, value96, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value65, value100, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value65, value100, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 100 = false ∨ valuation q 127 = false := by
  rw [value65, value100, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (406 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value65, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 65 = false ∨ valuation q 103 = false ∨ valuation q 127 = false := by
  rw [value65, value103, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value96, value100, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value96, value100, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 127 = false := by
  rw [value96, value100, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 96 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value96, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 96 = false ∨ valuation q 103 = false ∨ valuation q 127 = false := by
  rw [value96, value103, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 96 = false ∨ valuation q 107 = false ∨ valuation q 127 = false := by
  rw [value96, value106, value107, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value100, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 127 = false := by
  rw [value100, value103, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 100 = false ∨ valuation q 107 = false ∨ valuation q 127 = false := by
  rw [value100, value106, value107, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 127 = false := by
  rw [value103, value106, value107, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (410 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 233 = true ∨ valuation q 30 = true ∨ valuation q 65 = true ∨ valuation q 96 = true ∨ valuation q 100 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value30, value65, value96, value100, value103, value106, value107, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(158 : Vertex), (286 : Vertex), (398 : Vertex), (406 : Vertex), (410 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (478 : Vertex) [(158 : Vertex), (286 : Vertex), (398 : Vertex), (406 : Vertex), (410 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 31 = false ∨ valuation q 66 = false ∨ valuation q 104 = false := by
  rw [value31, value66, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (287 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 31 = false ∨ valuation q 66 = false ∨ valuation q 105 = false := by
  rw [value31, value66, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (287 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E052.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112052
