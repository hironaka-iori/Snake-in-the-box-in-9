import E112234Semantics
import B112E234Inputs
namespace Snake9.Regrowth.E112234
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 8 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value8, value16, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value16, value17, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 80 = false := by
  rw [value16, value17, value18, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 80 = false := by
  rw [value16, value17, value21, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (184 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 80 = false := by
  rw [value16, value18, value21, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (178 : Vertex) (184 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value9, value16, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 119 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value16, value17, value19, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(176 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (161 : Vertex) [(176 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 10 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value10, value16, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 10 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value10, value16, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value10, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value16, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 120 = true ∨ valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 20 = true := by
  rw [value16, value18, value19, value20, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(176 : Vertex), (179 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (162 : Vertex) [(176 : Vertex), (179 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 121 = true ∨ valuation q 17 = true ∨ valuation q 18 = true := by
  rw [value17, value18, value19, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(177 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (163 : Vertex) [(177 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 121 = true ∨ valuation q 11 = true ∨ valuation q 18 = true := by
  rw [value11, value18, value19, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(163 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (177 : Vertex) [(163 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 121 = true ∨ valuation q 11 = true ∨ valuation q 17 = true := by
  rw [value11, value17, value19, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(163 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (178 : Vertex) [(163 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 122 = true ∨ valuation q 24 = true := by
  rw [value20, value24, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (178 : Vertex) [(190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 122 = true ∨ valuation q 18 = true := by
  rw [value18, value20, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(178 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (190 : Vertex) [(178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 16 = false ∨ valuation q 22 = false ∨ valuation q 37 = false := by
  rw [value16, value21, value22, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 123 = true ∨ valuation q 16 = true ∨ valuation q 22 = true := by
  rw [value16, value21, value22, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(176 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (248 : Vertex) [(176 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value21, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (184 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 124 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value22, value23, value24, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (184 : Vertex) [(189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 124 = true ∨ valuation q 21 = true ∨ valuation q 24 = true := by
  rw [value21, value22, value24, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(184 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(184 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 124 = true ∨ valuation q 21 = true ∨ valuation q 23 = true := by
  rw [value21, value22, value23, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(184 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (190 : Vertex) [(184 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value14, value22, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value20, value22, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 40 = false := by
  rw [value15, value24, value25, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 86 = false := by
  rw [value15, value24, value25, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (190 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value10, value26, value27, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 129 = true ∨ valuation q 11 = true ∨ valuation q 26 = true ∨ valuation q 31 = true := by
  rw [value11, value26, value27, value31, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(163 : Vertex), (226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (99 : Vertex) [(163 : Vertex), (226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value28, value29, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 35 = true := by
  rw [value12, value29, value35, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(165 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (228 : Vertex) [(165 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 28 = true := by
  rw [value12, value28, value29, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(165 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (245 : Vertex) [(165 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E234.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112234
