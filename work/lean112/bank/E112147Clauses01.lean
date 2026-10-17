import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 122 = true ∨ valuation q 12 = true ∨ valuation q 23 = true := by
  rw [value12, value22, value23, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(168 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (186 : Vertex) [(168 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 26 = false := by
  rw [value13, value22, value23, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (184 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value13, value23, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (187 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value22, value23, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (184 : Vertex) (187 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value14, value22, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (170 : Vertex) (184 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 124 = true ∨ valuation q 22 = true ∨ valuation q 25 = true := by
  rw [value22, value24, value25, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(184 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (170 : Vertex) [(184 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 126 = true ∨ valuation q 23 = true := by
  rw [value23, value26, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(185 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (181 : Vertex) [(185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 126 = true ∨ valuation q 19 = true := by
  rw [value19, value26, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(181 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (185 : Vertex) [(181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 9 = false ∨ valuation q 31 = false ∨ valuation q 35 = false := by
  rw [value9, value27, value31, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (160 : Vertex) (232 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 35 = false := by
  rw [value27, value28, value31, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (225 : Vertex) (232 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 128 = true ∨ valuation q 27 = true ∨ valuation q 32 = true := by
  rw [value27, value28, value32, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(224 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (229 : Vertex) [(224 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 129 = true ∨ valuation q 28 = true := by
  rw [value28, value29, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(225 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (231 : Vertex) [(225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 130 = true ∨ valuation q 34 = true := by
  rw [value30, value34, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (231 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(239 : Vertex)] := by decide
  have hg := other_cover q (231 : Vertex) (229 : Vertex) [(239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 130 = true ∨ valuation q 29 = true := by
  rw [value29, value30, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (231 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(229 : Vertex)] := by decide
  have hg := other_cover q (231 : Vertex) (239 : Vertex) [(229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 13 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value13, value28, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (169 : Vertex) (225 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 40 = false := by
  rw [value16, value33, value34, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (174 : Vertex) (239 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 133 = true ∨ valuation q 16 = true ∨ valuation q 40 = true := by
  rw [value16, value33, value40, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(174 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (239 : Vertex) [(174 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 41 = false := by
  rw [value30, value33, value34, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (231 : Vertex) (238 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 134 = true ∨ valuation q 30 = true ∨ valuation q 41 = true := by
  rw [value30, value34, value41, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(231 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (238 : Vertex) [(231 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 134 = true ∨ valuation q 30 = true ∨ valuation q 33 = true := by
  rw [value30, value33, value34, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(231 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (255 : Vertex) [(231 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 27 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value27, value35, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (224 : Vertex) (242 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 135 = true ∨ valuation q 27 = true ∨ valuation q 38 = true := by
  rw [value27, value35, value38, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(224 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (242 : Vertex) [(224 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 135 = true ∨ valuation q 27 = true ∨ valuation q 36 = true := by
  rw [value27, value35, value36, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(224 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (244 : Vertex) [(224 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 136 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(243 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (240 : Vertex) [(243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 136 = true ∨ valuation q 35 = true := by
  rw [value35, value36, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(240 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (243 : Vertex) [(240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 137 = true ∨ valuation q 36 = true := by
  rw [value36, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(242 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (179 : Vertex) [(242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 137 = true ∨ valuation q 17 = true := by
  rw [value17, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(179 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (242 : Vertex) [(179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 18 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value18, value35, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (180 : Vertex) (240 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 138 = true ∨ valuation q 18 = true ∨ valuation q 39 = true := by
  rw [value18, value38, value39, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(180 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (240 : Vertex) [(180 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 139 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(254 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (244 : Vertex) [(254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 139 = true ∨ valuation q 38 = true := by
  rw [value38, value39, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(244 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (254 : Vertex) [(244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 33 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value33, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (238 : Vertex) (252 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E147.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112147
