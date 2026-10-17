import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 107 = false ∨ valuation q 116 = false ∨ valuation q 123 = false := by
  rw [value107, value116, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (454 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 107 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value107, value117, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (454 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value116, value117, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (466 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 107 = true ∨ valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 123 = true := by
  rw [value107, value116, value117, value119, value123, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (470 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(454 : Vertex), (466 : Vertex), (468 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (470 : Vertex) (214 : Vertex) [(454 : Vertex), (466 : Vertex), (468 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 61 = true ∨ valuation q 107 = true ∨ valuation q 117 = true ∨ valuation q 123 = true := by
  rw [value61, value107, value117, value119, value123, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (470 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(214 : Vertex), (454 : Vertex), (468 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (470 : Vertex) (466 : Vertex) [(214 : Vertex), (454 : Vertex), (468 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 61 = true ∨ valuation q 107 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value61, value107, value116, value117, value119, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (470 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(214 : Vertex), (454 : Vertex), (466 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (470 : Vertex) (478 : Vertex) [(214 : Vertex), (454 : Vertex), (466 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 99 = false ∨ valuation q 116 = false ∨ valuation q 123 = false := by
  rw [value99, value116, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (410 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 116 = true ∨ valuation q 123 = true := by
  rw [value116, value120, value123, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(466 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (410 : Vertex) [(466 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 99 = true ∨ valuation q 123 = true := by
  rw [value99, value120, value123, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(410 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (466 : Vertex) [(410 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 99 = true ∨ valuation q 116 = true := by
  rw [value99, value116, value120, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(410 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (478 : Vertex) [(410 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 83 = false ∨ valuation q 101 = false := by
  rw [value66, value83, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (348 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 83 = false ∨ valuation q 110 = false := by
  rw [value66, value83, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (348 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 83 = false ∨ valuation q 117 = false := by
  rw [value66, value83, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (348 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 83 = false ∨ valuation q 122 = false := by
  rw [value66, value83, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (348 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 83 = false ∨ valuation q 123 = false := by
  rw [value66, value83, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (348 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 110 = false := by
  rw [value66, value101, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value66, value101, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (412 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value66, value101, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (412 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 123 = false := by
  rw [value66, value101, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (412 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value66, value110, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value66, value110, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (460 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 110 = false ∨ valuation q 123 = false := by
  rw [value66, value110, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value66, value117, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value66, value117, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 66 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value66, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (220 : Vertex) (477 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 101 = false ∨ valuation q 110 = false := by
  rw [value83, value101, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value83, value101, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (412 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value83, value101, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (412 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 101 = false ∨ valuation q 123 = false := by
  rw [value83, value101, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (412 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value83, value110, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value83, value110, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (460 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 110 = false ∨ valuation q 123 = false := by
  rw [value83, value110, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E105.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112105
