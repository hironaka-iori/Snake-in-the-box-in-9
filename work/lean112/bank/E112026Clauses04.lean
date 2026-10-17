import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 48 = false := by
  rw [value29, value30, value31, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value14, value32, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (227 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value14, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value32, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (227 : Vertex) (230 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 153 = true ∨ valuation q 14 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value14, value32, value33, value36, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(162 : Vertex), (227 : Vertex), (230 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (234 : Vertex) [(162 : Vertex), (227 : Vertex), (230 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 154 = true ∨ valuation q 15 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value15, value32, value33, value38, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(163 : Vertex), (226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (99 : Vertex) [(163 : Vertex), (226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 154 = true ∨ valuation q 9 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value9, value32, value33, value38, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(99 : Vertex), (226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (163 : Vertex) [(99 : Vertex), (226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 10 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value10, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (229 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 10 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value10, value34, value35, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (229 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 39 = false := by
  rw [value34, value35, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value34, value35, value36, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value34, value35, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value34, value36, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 42 = false := by
  rw [value16, value34, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (165 : Vertex) (228 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 156 = true ∨ valuation q 16 = true ∨ valuation q 42 = true := by
  rw [value16, value35, value42, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(165 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (228 : Vertex) [(165 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 156 = true ∨ valuation q 16 = true ∨ valuation q 34 = true := by
  rw [value16, value34, value35, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(165 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (245 : Vertex) [(165 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 40 = true ∨ valuation q 106 = true := by
  rw [value32, value34, value36, value40, value106, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(226 : Vertex), (228 : Vertex), (238 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (166 : Vertex) [(226 : Vertex), (228 : Vertex), (238 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 157 = true ∨ valuation q 17 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 106 = true := by
  rw [value17, value32, value34, value36, value106, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(166 : Vertex), (226 : Vertex), (228 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (238 : Vertex) [(166 : Vertex), (226 : Vertex), (228 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 157 = true ∨ valuation q 17 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 40 = true := by
  rw [value17, value32, value34, value36, value40, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(166 : Vertex), (226 : Vertex), (228 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (486 : Vertex) [(166 : Vertex), (226 : Vertex), (228 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value37, value38, value40, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (235 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 158 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 46 = true := by
  rw [value37, value38, value40, value46, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(235 : Vertex), (238 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (226 : Vertex) [(235 : Vertex), (238 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 158 = true ∨ valuation q 32 = true ∨ valuation q 38 = true ∨ valuation q 46 = true := by
  rw [value32, value37, value38, value46, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (238 : Vertex) [(226 : Vertex), (235 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 158 = true ∨ valuation q 32 = true ∨ valuation q 38 = true ∨ valuation q 40 = true := by
  rw [value32, value37, value38, value40, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (250 : Vertex) [(226 : Vertex), (235 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value19, value33, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 47 = false := by
  rw [value19, value33, value38, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 110 = false := by
  rw [value19, value33, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 37 = false ∨ valuation q 47 = false := by
  rw [value19, value37, value38, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 37 = false ∨ valuation q 110 = false := by
  rw [value19, value37, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 19 = false ∨ valuation q 47 = false ∨ valuation q 110 = false := by
  rw [value19, value38, value47, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (251 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 47 = false := by
  rw [value33, value37, value38, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 110 = false := by
  rw [value33, value37, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 47 = false ∨ valuation q 110 = false := by
  rw [value33, value38, value47, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (251 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E026.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112026
