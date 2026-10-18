import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 17 = false ∨ valuation q 31 = false := by
  rw [value11, value12, value17, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value11, value13, value17, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 31 = false := by
  rw [value11, value13, value17, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 31 = false := by
  rw [value11, value17, value21, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 21 = true ∨ valuation q 31 = true := by
  rw [value11, value12, value13, value21, value31, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(161 : Vertex), (162 : Vertex), (176 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (168 : Vertex) [(161 : Vertex), (162 : Vertex), (176 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 31 = true := by
  rw [value11, value12, value13, value17, value31, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(161 : Vertex), (162 : Vertex), (168 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (176 : Vertex) [(161 : Vertex), (162 : Vertex), (168 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 15 = true ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value11, value12, value14, value15, value22, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ∈ [(160 : Vertex), (163 : Vertex), (165 : Vertex), (177 : Vertex), (225 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (161 : Vertex) [(160 : Vertex), (163 : Vertex), (165 : Vertex), (177 : Vertex), (225 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 22 = false := by
  rw [value11, value12, value15, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 22 = false ∨ valuation q 32 = false := by
  rw [value11, value12, value22, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (177 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 14 = true ∨ valuation q 15 = true ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value12, value14, value15, value22, value32, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(163 : Vertex), (165 : Vertex), (177 : Vertex), (225 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(163 : Vertex), (165 : Vertex), (177 : Vertex), (225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value11, value12, value15, value22, value32, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(160 : Vertex), (165 : Vertex), (177 : Vertex), (225 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (163 : Vertex) [(160 : Vertex), (165 : Vertex), (177 : Vertex), (225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value11, value12, value14, value22, value32, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (177 : Vertex), (225 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (165 : Vertex) [(160 : Vertex), (163 : Vertex), (177 : Vertex), (225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 15 = true ∨ valuation q 32 = true := by
  rw [value11, value12, value14, value15, value32, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (165 : Vertex), (225 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (177 : Vertex) [(160 : Vertex), (163 : Vertex), (165 : Vertex), (225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value11, value13, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 82 = false := by
  rw [value11, value13, value14, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 16 = false ∨ valuation q 82 = false := by
  rw [value11, value13, value16, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (166 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 23 = false ∨ valuation q 82 = false := by
  rw [value11, value13, value23, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 18 = false := by
  rw [value12, value13, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 24 = false := by
  rw [value12, value13, value14, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 83 = false := by
  rw [value12, value13, value14, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 24 = false := by
  rw [value12, value14, value18, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 83 = false := by
  rw [value12, value14, value18, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (171 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 24 = false := by
  rw [value13, value14, value18, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 83 = false := by
  rw [value13, value14, value18, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (171 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 83 = false := by
  rw [value14, value18, value24, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (171 : Vertex) (179 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 19 = false ∨ valuation q 35 = false := by
  rw [value12, value15, value19, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 19 = false ∨ valuation q 85 = false := by
  rw [value12, value15, value19, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 35 = false ∨ valuation q 85 = false := by
  rw [value12, value15, value35, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (229 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 35 = false ∨ valuation q 85 = false := by
  rw [value15, value19, value35, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (173 : Vertex) (229 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 35 = true ∨ valuation q 85 = true := by
  rw [value12, value15, value35, value85, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(161 : Vertex), (229 : Vertex), (421 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (173 : Vertex) [(161 : Vertex), (229 : Vertex), (421 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 36 = false := by
  rw [value13, value16, value25, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (182 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 132 = true ∨ valuation q 13 = true ∨ valuation q 36 = true := by
  rw [value13, value16, value36, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(162 : Vertex), (230 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (182 : Vertex) [(162 : Vertex), (230 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E169.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112169
