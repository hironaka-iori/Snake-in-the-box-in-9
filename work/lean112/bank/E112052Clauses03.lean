import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value15, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (145 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value15, value24, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (145 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 15 = false ∨ valuation q 25 = false ∨ valuation q 27 = false := by
  rw [value15, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (146 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 27 = false := by
  rw [value24, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (145 : Vertex) (146 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 44 = false := by
  rw [value26, value27, value31, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (147 : Vertex) (159 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 101 = false := by
  rw [value26, value27, value31, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (147 : Vertex) (159 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 31 = false ∨ valuation q 44 = false ∨ valuation q 101 = false := by
  rw [value27, value31, value44, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (159 : Vertex) (215 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 31 = true ∨ valuation q 44 = true ∨ valuation q 101 = true := by
  rw [value27, value31, value44, value101, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(159 : Vertex), (215 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (147 : Vertex) [(159 : Vertex), (215 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 26 = true ∨ valuation q 44 = true ∨ valuation q 101 = true := by
  rw [value26, value27, value44, value101, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(147 : Vertex), (215 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (159 : Vertex) [(147 : Vertex), (215 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 26 = true ∨ valuation q 31 = true ∨ valuation q 101 = true := by
  rw [value26, value27, value31, value101, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(147 : Vertex), (159 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (215 : Vertex) [(147 : Vertex), (159 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 26 = true ∨ valuation q 31 = true ∨ valuation q 44 = true := by
  rw [value26, value27, value31, value44, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(147 : Vertex), (159 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (407 : Vertex) [(147 : Vertex), (159 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 29 = true := by
  rw [value28, value29, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(156 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (144 : Vertex) [(156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 23 = true := by
  rw [value23, value28, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (156 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value20, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (140 : Vertex) (152 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 28 = true ∨ valuation q 30 = true := by
  rw [value28, value29, value30, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(152 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (140 : Vertex) [(152 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 20 = true ∨ valuation q 30 = true := by
  rw [value20, value29, value30, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(140 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (152 : Vertex) [(140 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 22 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value22, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (142 : Vertex) (156 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 22 = false ∨ valuation q 31 = false ∨ valuation q 106 = false := by
  rw [value22, value30, value31, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (142 : Vertex) (159 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 106 = false := by
  rw [value29, value30, value31, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (156 : Vertex) (159 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 29 = true ∨ valuation q 31 = true ∨ valuation q 106 = true := by
  rw [value29, value30, value31, value106, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(156 : Vertex), (159 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (142 : Vertex) [(156 : Vertex), (159 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 22 = true ∨ valuation q 31 = true ∨ valuation q 106 = true := by
  rw [value22, value30, value31, value106, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(142 : Vertex), (159 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (156 : Vertex) [(142 : Vertex), (159 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 22 = true ∨ valuation q 29 = true ∨ valuation q 106 = true := by
  rw [value22, value29, value30, value106, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(142 : Vertex), (156 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (159 : Vertex) [(142 : Vertex), (156 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 22 = true ∨ valuation q 29 = true ∨ valuation q 31 = true := by
  rw [value22, value29, value30, value31, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(142 : Vertex), (156 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (414 : Vertex) [(142 : Vertex), (156 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 107 = false := by
  rw [value27, value30, value31, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (151 : Vertex) (158 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 30 = true ∨ valuation q 107 = true := by
  rw [value30, value31, value107, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(158 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (151 : Vertex) [(158 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 27 = true ∨ valuation q 107 = true := by
  rw [value27, value31, value107, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(151 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(151 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value27, value30, value31, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(151 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (415 : Vertex) [(151 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 108 = false := by
  rw [value32, value33, value36, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 33 = true ∨ valuation q 108 = true := by
  rw [value32, value33, value108, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(194 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(194 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value32, value33, value36, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(194 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (448 : Vertex) [(194 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 2 = false ∨ valuation q 14 = false ∨ valuation q 32 = false := by
  rw [value2, value14, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 2 = false ∨ valuation q 14 = false ∨ valuation q 34 = false := by
  rw [value2, value14, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E052.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112052
