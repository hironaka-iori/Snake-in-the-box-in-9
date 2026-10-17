import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value94, value110, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value94, value114, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 110 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value110, value114, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value114, value118, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (459 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide)

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 94 = true ∨ valuation q 114 = true ∨ valuation q 118 = true := by
  rw [value94, value114, value115, value118, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(395 : Vertex), (457 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (451 : Vertex) [(395 : Vertex), (457 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 94 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value94, value110, value115, value118, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(395 : Vertex), (451 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (457 : Vertex) [(395 : Vertex), (451 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 94 = true ∨ valuation q 110 = true ∨ valuation q 114 = true := by
  rw [value94, value110, value114, value115, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(395 : Vertex), (451 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (463 : Vertex) [(395 : Vertex), (451 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value95, value112, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value95, value112, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 112 = false ∨ valuation q 126 = false := by
  rw [value95, value112, value116, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (453 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value95, value114, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 114 = false ∨ valuation q 126 = false := by
  rw [value95, value114, value116, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value95, value116, value118, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 112 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value112, value114, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 112 = false ∨ valuation q 114 = false ∨ valuation q 126 = false := by
  rw [value112, value114, value116, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 112 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value112, value116, value118, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 114 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value114, value116, value118, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (457 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 243 = true ∨ valuation q 95 = true ∨ valuation q 112 = true ∨ valuation q 118 = true ∨ valuation q 126 = true := by
  rw [value95, value112, value116, value118, value126, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(397 : Vertex), (453 : Vertex), (463 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (457 : Vertex) [(397 : Vertex), (453 : Vertex), (463 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 243 = true ∨ valuation q 95 = true ∨ valuation q 112 = true ∨ valuation q 114 = true ∨ valuation q 126 = true := by
  rw [value95, value112, value114, value116, value126, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(397 : Vertex), (453 : Vertex), (457 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (463 : Vertex) [(397 : Vertex), (453 : Vertex), (457 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 96 = false ∨ valuation q 118 = false := by
  rw [value39, value96, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 96 = false ∨ valuation q 127 = false := by
  rw [value39, value96, value117, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 118 = false ∨ valuation q 127 = false := by
  rw [value39, value117, value118, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 118 = false ∨ valuation q 127 = false := by
  rw [value96, value117, value118, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 244 = true ∨ valuation q 39 = true ∨ valuation q 96 = true ∨ valuation q 127 = true := by
  rw [value39, value96, value117, value127, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(206 : Vertex), (398 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (463 : Vertex) [(206 : Vertex), (398 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 244 = true ∨ valuation q 39 = true ∨ valuation q 96 = true ∨ valuation q 118 = true := by
  rw [value39, value96, value117, value118, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(206 : Vertex), (398 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (478 : Vertex) [(206 : Vertex), (398 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value113, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (459 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 113 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value113, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value115, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value115, value116, value117, value118, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(459 : Vertex), (461 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (455 : Vertex) [(459 : Vertex), (461 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 113 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value113, value116, value117, value118, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(455 : Vertex), (461 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (459 : Vertex) [(455 : Vertex), (461 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 113 = true ∨ valuation q 115 = true ∨ valuation q 117 = true := by
  rw [value113, value115, value117, value118, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (461 : Vertex) [(455 : Vertex), (459 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 113 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value113, value115, value116, value118, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (462 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block27 (q : Snake 81) (h : Conditions q) : B112E052.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112052
