import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 36 = true := by
  rw [value32, value35, value36, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(180 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (190 : Vertex) [(180 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 158 = true ∨ valuation q 35 = true := by
  rw [value35, value36, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(188 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value33, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (186 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value38, value39, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (227 : Vertex) (230 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 105 = false := by
  rw [value38, value39, value42, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (227 : Vertex) (230 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 105 = false := by
  rw [value38, value39, value43, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (227 : Vertex) (234 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 105 = false := by
  rw [value38, value42, value43, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (230 : Vertex) (234 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 17 = false ∨ valuation q 38 = false ∨ valuation q 106 = false := by
  rw [value17, value38, value39, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (226 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 161 = true ∨ valuation q 38 = true ∨ valuation q 44 = true ∨ valuation q 106 = true := by
  rw [value38, value39, value44, value106, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (99 : Vertex) [(226 : Vertex), (235 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 161 = true ∨ valuation q 17 = true ∨ valuation q 44 = true ∨ valuation q 106 = true := by
  rw [value17, value39, value44, value106, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(99 : Vertex), (235 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (226 : Vertex) [(99 : Vertex), (235 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 161 = true ∨ valuation q 17 = true ∨ valuation q 38 = true ∨ valuation q 106 = true := by
  rw [value17, value38, value39, value106, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(99 : Vertex), (226 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (235 : Vertex) [(99 : Vertex), (226 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 18 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value18, value40, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (229 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 18 = false ∨ valuation q 41 = false ∨ valuation q 47 = false := by
  rw [value18, value40, value41, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (229 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 18 = false ∨ valuation q 42 = false ∨ valuation q 47 = false := by
  rw [value18, value40, value42, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (230 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 18 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value18, value40, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 47 = false := by
  rw [value40, value41, value42, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value40, value41, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 40 = false ∨ valuation q 48 = false ∨ valuation q 107 = false := by
  rw [value40, value41, value48, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (228 : Vertex) (245 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 163 = true ∨ valuation q 40 = true ∨ valuation q 107 = true := by
  rw [value40, value41, value107, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(228 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (245 : Vertex) [(228 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 163 = true ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value40, value41, value48, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(228 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (485 : Vertex) [(228 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 165 = true ∨ valuation q 44 = true ∨ valuation q 46 = true ∨ valuation q 52 = true := by
  rw [value43, value44, value46, value52, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(235 : Vertex), (238 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (226 : Vertex) [(235 : Vertex), (238 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 165 = true ∨ valuation q 38 = true ∨ valuation q 44 = true ∨ valuation q 52 = true := by
  rw [value38, value43, value44, value52, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (238 : Vertex) [(226 : Vertex), (235 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 26 = false ∨ valuation q 43 = false ∨ valuation q 110 = false := by
  rw [value26, value43, value44, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 53 = false := by
  rw [value39, value43, value44, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 110 = false := by
  rw [value39, value43, value44, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 39 = false ∨ valuation q 53 = false ∨ valuation q 110 = false := by
  rw [value39, value44, value53, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (251 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 43 = false ∨ valuation q 53 = false ∨ valuation q 110 = false := by
  rw [value43, value44, value53, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (234 : Vertex) (251 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 167 = true ∨ valuation q 46 = true := by
  rw [value45, value46, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(238 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (228 : Vertex) [(238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 167 = true ∨ valuation q 40 = true := by
  rw [value40, value45, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(228 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (238 : Vertex) [(228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 168 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value42, value45, value46, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(230 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (234 : Vertex) [(230 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 168 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value42, value43, value46, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(230 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (236 : Vertex) [(230 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 32 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value32, value40, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (180 : Vertex) (228 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.First112
