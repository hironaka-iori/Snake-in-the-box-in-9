import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 16 = false ∨ valuation q 35 = false ∨ valuation q 109 = false := by
  rw [value16, value34, value35, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (164 : Vertex) (229 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 109 = false := by
  rw [value34, value35, value44, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = false ∨ valuation q 39 = false ∨ valuation q 110 = false := by
  rw [value34, value35, value39, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (228 : Vertex) (237 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 39 = true ∨ valuation q 110 = true := by
  rw [value35, value39, value110, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(237 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (228 : Vertex) [(237 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 34 = true ∨ valuation q 110 = true := by
  rw [value34, value35, value110, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(228 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (237 : Vertex) [(228 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 34 = true ∨ valuation q 39 = true := by
  rw [value34, value35, value39, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(228 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (485 : Vertex) [(228 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 20 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value20, value36, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (169 : Vertex) (235 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 20 = false ∨ valuation q 39 = false ∨ valuation q 114 = false := by
  rw [value20, value36, value39, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (169 : Vertex) (237 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 114 = false := by
  rw [value36, value38, value39, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (235 : Vertex) (237 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 114 = true := by
  rw [value36, value38, value39, value114, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(235 : Vertex), (237 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (169 : Vertex) [(235 : Vertex), (237 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 20 = true ∨ valuation q 39 = true ∨ valuation q 114 = true := by
  rw [value20, value36, value39, value114, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(169 : Vertex), (237 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (235 : Vertex) [(169 : Vertex), (237 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 20 = true ∨ valuation q 38 = true ∨ valuation q 114 = true := by
  rw [value20, value36, value38, value114, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(169 : Vertex), (235 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (237 : Vertex) [(169 : Vertex), (235 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 20 = true ∨ valuation q 38 = true ∨ valuation q 39 = true := by
  rw [value20, value36, value38, value39, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(169 : Vertex), (235 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (489 : Vertex) [(169 : Vertex), (235 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 32 = false ∨ valuation q 38 = false ∨ valuation q 115 = false := by
  rw [value32, value37, value38, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (226 : Vertex) (235 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 165 = true ∨ valuation q 38 = true ∨ valuation q 115 = true := by
  rw [value37, value38, value115, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(235 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (226 : Vertex) [(235 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 165 = true ∨ valuation q 32 = true ∨ valuation q 115 = true := by
  rw [value32, value37, value115, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(226 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (235 : Vertex) [(226 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 165 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value32, value37, value38, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (490 : Vertex) [(226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 21 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value21, value33, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 21 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value21, value33, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 21 = false ∨ valuation q 33 = false ∨ valuation q 40 = false := by
  rw [value21, value33, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 21 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value21, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (233 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 21 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value21, value36, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (233 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 21 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value21, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value33, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (233 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value33, value36, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (233 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value33, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value36, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (233 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 166 = true ∨ valuation q 21 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 40 = true := by
  rw [value21, value33, value36, value38, value40, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(171 : Vertex), (227 : Vertex), (233 : Vertex), (239 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (234 : Vertex) [(171 : Vertex), (227 : Vertex), (233 : Vertex), (239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value35, value36, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (229 : Vertex) (233 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 117 = false := by
  rw [value35, value36, value39, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (229 : Vertex) (233 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 117 = false := by
  rw [value35, value39, value40, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (229 : Vertex) (239 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 117 = false := by
  rw [value36, value39, value40, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (233 : Vertex) (239 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E034.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112034
