import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 133 = true ∨ valuation q 13 = true ∨ valuation q 20 = true := by
  rw [value13, value20, value22, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(132 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (150 : Vertex) [(132 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value21, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (146 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 134 = true ∨ valuation q 22 = true ∨ valuation q 24 = true := by
  rw [value22, value23, value24, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(148 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (146 : Vertex) [(148 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 134 = true ∨ valuation q 21 = true ∨ valuation q 24 = true := by
  rw [value21, value23, value24, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(146 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (148 : Vertex) [(146 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 134 = true ∨ valuation q 21 = true ∨ valuation q 22 = true := by
  rw [value21, value22, value23, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(146 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (151 : Vertex) [(146 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 24 = true := by
  rw [value24, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (151 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 36 = false := by
  rw [value15, value23, value24, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (135 : Vertex) (150 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 91 = false := by
  rw [value15, value23, value24, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (135 : Vertex) (150 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 135 = true ∨ valuation q 15 = true ∨ valuation q 23 = true ∨ valuation q 91 = true := by
  rw [value15, value23, value24, value91, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(135 : Vertex), (150 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (215 : Vertex) [(135 : Vertex), (150 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 25 = true := by
  rw [value25, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (152 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 20 = true ∨ valuation q 26 = true ∨ valuation q 27 = true := by
  rw [value20, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ∈ [(144 : Vertex), (153 : Vertex), (154 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (152 : Vertex) [(144 : Vertex), (153 : Vertex), (154 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 20 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value20, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (144 : Vertex) (153 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value26, value27, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (152 : Vertex) (153 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 136 = true ∨ valuation q 26 = true ∨ valuation q 27 = true := by
  rw [value25, value26, value27, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(153 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (144 : Vertex) [(153 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 136 = true ∨ valuation q 20 = true ∨ valuation q 27 = true := by
  rw [value20, value25, value27, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(144 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (153 : Vertex) [(144 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 136 = true ∨ valuation q 20 = true ∨ valuation q 26 = true := by
  rw [value20, value25, value26, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(144 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (154 : Vertex) [(144 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 137 = true ∨ valuation q 25 = true := by
  rw [value25, value26, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(152 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (137 : Vertex) [(152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 137 = true ∨ valuation q 16 = true := by
  rw [value16, value26, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(137 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (152 : Vertex) [(137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 25 = false := by
  rw [value17, value21, value25, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (146 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 138 = true ∨ valuation q 21 = true ∨ valuation q 25 = true := by
  rw [value21, value25, value27, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(146 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (138 : Vertex) [(146 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 138 = true ∨ valuation q 17 = true ∨ valuation q 25 = true := by
  rw [value17, value25, value27, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(138 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (146 : Vertex) [(138 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 138 = true ∨ valuation q 17 = true ∨ valuation q 21 = true := by
  rw [value17, value21, value27, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(138 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (152 : Vertex) [(138 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value28, value29, value30, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (196 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 139 = true ∨ valuation q 30 = true ∨ valuation q 33 = true := by
  rw [value28, value30, value33, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(196 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (194 : Vertex) [(196 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 139 = true ∨ valuation q 29 = true ∨ valuation q 33 = true := by
  rw [value28, value29, value33, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (196 : Vertex) [(194 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 139 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value28, value29, value30, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(194 : Vertex), (196 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (208 : Vertex) [(194 : Vertex), (196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 28 = true := by
  rw [value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ∈ [(192 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (194 : Vertex) [(192 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 140 = true := by
  rw [value29, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (194 : Vertex) (192 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 13 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value13, value28, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (132 : Vertex) (192 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 141 = true ∨ valuation q 28 = true ∨ valuation q 31 = true := by
  rw [value28, value30, value31, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(192 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (132 : Vertex) [(192 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 141 = true ∨ valuation q 13 = true ∨ valuation q 31 = true := by
  rw [value13, value30, value31, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(132 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (192 : Vertex) [(132 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 141 = true ∨ valuation q 13 = true ∨ valuation q 28 = true := by
  rw [value13, value28, value30, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(132 : Vertex), (192 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (197 : Vertex) [(132 : Vertex), (192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E161.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112161
