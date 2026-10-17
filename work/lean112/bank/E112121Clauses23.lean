import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 224 = true ∨ valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 97 = true := by
  rw [value92, value95, value97, value98, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(422 : Vertex), (426 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (431 : Vertex) [(422 : Vertex), (426 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 77 = false ∨ valuation q 93 = false := by
  rw [value51, value77, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (303 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 77 = false ∨ valuation q 96 = false := by
  rw [value51, value77, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (303 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 77 = false ∨ valuation q 98 = false := by
  rw [value51, value77, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (303 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 77 = false ∨ valuation q 109 = false := by
  rw [value51, value77, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (303 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 93 = false ∨ valuation q 109 = false := by
  rw [value51, value93, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (423 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value51, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value51, value96, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (427 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value51, value98, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (430 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 98 = false ∨ valuation q 118 = false := by
  rw [value51, value98, value99, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value51, value99, value109, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value77, value93, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value77, value93, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 93 = false ∨ valuation q 109 = false := by
  rw [value77, value93, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 93 = false ∨ valuation q 118 = false := by
  rw [value77, value93, value99, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value77, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value77, value96, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (427 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 118 = false := by
  rw [value77, value96, value99, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (427 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value77, value98, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (430 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 98 = false ∨ valuation q 118 = false := by
  rw [value77, value98, value99, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 77 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value77, value99, value109, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value93, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value93, value96, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (427 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value93, value98, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (430 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value96, value98, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (430 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 118 = false := by
  rw [value96, value98, value99, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value96, value99, value109, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 98 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value98, value99, value109, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (430 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 78 = false ∨ valuation q 88 = false := by
  rw [value53, value78, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 78 = false ∨ valuation q 101 = false := by
  rw [value53, value78, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 78 = false ∨ valuation q 103 = false := by
  rw [value53, value78, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 53 = false ∨ valuation q 78 = false ∨ valuation q 106 = false := by
  rw [value53, value78, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E121.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112121
