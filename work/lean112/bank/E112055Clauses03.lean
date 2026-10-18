import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value4, value13, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (5 : Vertex) (23 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 15 = false ∨ valuation q 33 = false := by
  rw [value4, value13, value15, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (5 : Vertex) (23 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 15 = false ∨ valuation q 50 = false := by
  rw [value4, value13, value15, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (5 : Vertex) (23 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 15 = false ∨ valuation q 83 = false := by
  rw [value4, value13, value15, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (5 : Vertex) (23 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value4, value13, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (5 : Vertex) (29 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 19 = false ∨ valuation q 83 = false := by
  rw [value4, value13, value19, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (5 : Vertex) (29 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 33 = false ∨ valuation q 50 = false := by
  rw [value4, value13, value33, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (5 : Vertex) (85 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 33 = false ∨ valuation q 83 = false := by
  rw [value4, value13, value33, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (5 : Vertex) (85 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value10, value13, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (23 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 33 = false := by
  rw [value10, value13, value15, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (23 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 83 = false := by
  rw [value10, value13, value15, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (23 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value10, value13, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (29 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 83 = false := by
  rw [value10, value13, value19, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (29 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 33 = false ∨ valuation q 83 = false := by
  rw [value10, value13, value33, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (85 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 50 = false ∨ valuation q 83 = false := by
  rw [value10, value13, value50, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (149 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value13, value15, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (23 : Vertex) (29 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 83 = false := by
  rw [value13, value15, value19, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (23 : Vertex) (29 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 33 = false ∨ valuation q 83 = false := by
  rw [value13, value15, value33, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (23 : Vertex) (85 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 83 = false := by
  rw [value13, value19, value33, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (29 : Vertex) (85 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 14 = true := by
  rw [value14, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (22 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 51 = true ∨ valuation q 84 = true := by
  rw [value11, value14, value15, value51, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ∈ [(18 : Vertex), (23 : Vertex), (150 : Vertex), (278 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (22 : Vertex) [(18 : Vertex), (23 : Vertex), (150 : Vertex), (278 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 84 = false := by
  rw [value11, value14, value15, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (18 : Vertex) (23 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = false ∨ valuation q 51 = false ∨ valuation q 84 = false := by
  rw [value11, value14, value51, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (18 : Vertex) (150 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 15 = true ∨ valuation q 51 = true ∨ valuation q 84 = true := by
  rw [value14, value15, value51, value84, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(23 : Vertex), (150 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(23 : Vertex), (150 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 11 = true ∨ valuation q 51 = true ∨ valuation q 84 = true := by
  rw [value11, value14, value51, value84, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(18 : Vertex), (150 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (23 : Vertex) [(18 : Vertex), (150 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 84 = true := by
  rw [value11, value14, value15, value84, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(18 : Vertex), (23 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (150 : Vertex) [(18 : Vertex), (23 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 51 = true := by
  rw [value11, value14, value15, value51, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(18 : Vertex), (23 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (278 : Vertex) [(18 : Vertex), (23 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value12, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (21 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 20 = false := by
  rw [value12, value13, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (21 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 52 = false := by
  rw [value12, value13, value15, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (21 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 85 = false := by
  rw [value12, value13, value15, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (21 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value12, value14, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (22 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E055.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112055
