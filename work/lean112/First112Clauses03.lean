import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 89 = false := by
  rw [value25, value26, value28, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (169 : Vertex) (175 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 148 = true ∨ valuation q 7 = true ∨ valuation q 25 = true ∨ valuation q 44 = true ∨ valuation q 89 = true := by
  rw [value7, value25, value26, value44, value89, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(43 : Vertex), (169 : Vertex), (235 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (175 : Vertex) [(43 : Vertex), (169 : Vertex), (235 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value25, value27, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (169 : Vertex) (175 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 149 = true ∨ valuation q 25 = true ∨ valuation q 36 = true := by
  rw [value25, value27, value36, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(169 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(169 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 149 = true ∨ valuation q 25 = true ∨ valuation q 28 = true := by
  rw [value25, value27, value28, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(169 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (189 : Vertex) [(169 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value23, value26, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (171 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 92 = false := by
  rw [value23, value26, value28, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (171 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 23 = false ∨ valuation q 27 = false ∨ valuation q 92 = false := by
  rw [value23, value27, value28, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (173 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 92 = false := by
  rw [value26, value27, value28, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (171 : Vertex) (173 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 31 = false ∨ valuation q 93 = false := by
  rw [value21, value29, value31, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (179 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 151 = true ∨ valuation q 31 = true ∨ valuation q 93 = true := by
  rw [value29, value31, value93, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(179 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (161 : Vertex) [(179 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 151 = true ∨ valuation q 21 = true ∨ valuation q 93 = true := by
  rw [value21, value29, value93, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(161 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (179 : Vertex) [(161 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value30, value31, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (179 : Vertex) (182 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 152 = true ∨ valuation q 33 = true ∨ valuation q 34 = true := by
  rw [value30, value33, value34, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(182 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (179 : Vertex) [(182 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 30 = true ∨ valuation q 94 = true := by
  rw [value30, value31, value94, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(178 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (177 : Vertex) [(178 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 29 = true ∨ valuation q 94 = true := by
  rw [value29, value31, value94, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(177 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (178 : Vertex) [(177 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value29, value30, value31, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(177 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (435 : Vertex) [(177 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 10 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value10, value32, value33, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 10 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value10, value32, value35, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (188 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 10 = false ∨ valuation q 35 = false ∨ valuation q 95 = false := by
  rw [value10, value32, value35, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (188 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 10 = false ∨ valuation q 47 = false ∨ valuation q 95 = false := by
  rw [value10, value32, value47, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value32, value33, value35, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (182 : Vertex) (188 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 95 = false := by
  rw [value32, value33, value35, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (182 : Vertex) (188 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 47 = false ∨ valuation q 95 = false := by
  rw [value32, value33, value47, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (182 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 47 = false ∨ valuation q 95 = false := by
  rw [value32, value35, value47, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (188 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value22, value30, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (166 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 22 = false ∨ valuation q 32 = false ∨ valuation q 37 = false := by
  rw [value22, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (166 : Vertex) (180 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 155 = true ∨ valuation q 22 = true ∨ valuation q 30 = true ∨ valuation q 37 = true := by
  rw [value22, value30, value33, value37, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(166 : Vertex), (178 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (180 : Vertex) [(166 : Vertex), (178 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 156 = true ∨ valuation q 37 = true ∨ valuation q 52 = true ∨ valuation q 100 = true := by
  rw [value34, value37, value52, value100, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(190 : Vertex), (250 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (178 : Vertex) [(190 : Vertex), (250 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 156 = true ∨ valuation q 30 = true ∨ valuation q 37 = true ∨ valuation q 100 = true := by
  rw [value30, value34, value37, value100, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(178 : Vertex), (190 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (250 : Vertex) [(178 : Vertex), (190 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 156 = true ∨ valuation q 30 = true ∨ valuation q 37 = true ∨ valuation q 52 = true := by
  rw [value30, value34, value37, value52, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(178 : Vertex), (190 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (442 : Vertex) [(178 : Vertex), (190 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 37 = true := by
  rw [value32, value35, value37, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(180 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(180 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.First112
