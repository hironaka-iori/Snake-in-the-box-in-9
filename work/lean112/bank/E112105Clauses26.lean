import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 106 = false ∨ valuation q 122 = false := by
  rw [value60, value106, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (453 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value60, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (465 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 115 = false ∨ valuation q 122 = false := by
  rw [value60, value115, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (465 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value60, value117, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 95 = false ∨ valuation q 106 = false := by
  rw [value78, value95, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 95 = false ∨ valuation q 115 = false := by
  rw [value78, value95, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (405 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 95 = false ∨ valuation q 117 = false := by
  rw [value78, value95, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (405 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 95 = false ∨ valuation q 122 = false := by
  rw [value78, value95, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (405 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value78, value106, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value78, value106, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (453 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 106 = false ∨ valuation q 122 = false := by
  rw [value78, value106, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (453 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value78, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (465 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 115 = false ∨ valuation q 122 = false := by
  rw [value78, value115, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (465 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 78 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value78, value117, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (341 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 95 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value95, value106, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (405 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 95 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value95, value106, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (405 : Vertex) (453 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 95 = false ∨ valuation q 106 = false ∨ valuation q 122 = false := by
  rw [value95, value106, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (405 : Vertex) (453 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 95 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value95, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (405 : Vertex) (465 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 95 = false ∨ valuation q 115 = false ∨ valuation q 122 = false := by
  rw [value95, value115, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (405 : Vertex) (465 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 95 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value95, value117, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (405 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 106 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value106, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (465 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 106 = false ∨ valuation q 115 = false ∨ valuation q 122 = false := by
  rw [value106, value115, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (465 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 106 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value106, value117, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 115 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value115, value117, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (465 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 60 = true ∨ valuation q 78 = true ∨ valuation q 95 = true ∨ valuation q 106 = true ∨ valuation q 115 = true ∨ valuation q 117 = true := by
  rw [value60, value78, value95, value106, value115, value117, value118, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(213 : Vertex), (341 : Vertex), (405 : Vertex), (453 : Vertex), (465 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (477 : Vertex) [(213 : Vertex), (341 : Vertex), (405 : Vertex), (453 : Vertex), (465 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 61 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value61, value107, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (454 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 61 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value61, value107, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (454 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 61 = false ∨ valuation q 107 = false ∨ valuation q 123 = false := by
  rw [value61, value107, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (454 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 61 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value61, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 61 = false ∨ valuation q 116 = false ∨ valuation q 123 = false := by
  rw [value61, value116, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 61 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value61, value117, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 107 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value107, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (454 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E105.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112105
