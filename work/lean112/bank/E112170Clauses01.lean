import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 125 = true ∨ valuation q 24 = true ∨ valuation q 46 = true ∨ valuation q 74 = true := by
  rw [value24, value26, value46, value74, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(163 : Vertex), (235 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (175 : Vertex) [(163 : Vertex), (235 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 126 = true ∨ valuation q 28 = true ∨ valuation q 36 = true := by
  rw [value27, value28, value36, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(175 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (165 : Vertex) [(175 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 126 = true ∨ valuation q 25 = true ∨ valuation q 36 = true := by
  rw [value25, value27, value36, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(165 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(165 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 126 = true ∨ valuation q 25 = true ∨ valuation q 28 = true := by
  rw [value25, value27, value28, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(165 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (189 : Vertex) [(165 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 38 = false := by
  rw [value26, value27, value28, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (171 : Vertex) (173 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 127 = true ∨ valuation q 26 = true ∨ valuation q 38 = true := by
  rw [value26, value28, value38, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(171 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (173 : Vertex) [(171 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value21, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 34 = false := by
  rw [value29, value30, value31, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 47 = false := by
  rw [value29, value30, value31, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 22 = false ∨ valuation q 29 = false ∨ valuation q 32 = false := by
  rw [value22, value29, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 129 = true ∨ valuation q 22 = true ∨ valuation q 29 = true := by
  rw [value22, value29, value30, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (179 : Vertex) [(161 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 33 = false := by
  rw [value23, value29, value31, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value23, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value29, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 131 = true ∨ valuation q 24 = true ∨ valuation q 31 = true := by
  rw [value24, value31, value32, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(163 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (177 : Vertex) [(163 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 131 = true ∨ valuation q 24 = true ∨ valuation q 30 = true := by
  rw [value24, value30, value32, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(163 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (178 : Vertex) [(163 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 132 = true ∨ valuation q 31 = true := by
  rw [value31, value33, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(178 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (190 : Vertex) [(178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 29 = false ∨ valuation q 35 = false ∨ valuation q 80 = false := by
  rw [value29, value34, value35, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 27 = false ∨ valuation q 35 = false ∨ valuation q 38 = false := by
  rw [value27, value35, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 28 = false ∨ valuation q 36 = false ∨ valuation q 53 = false := by
  rw [value28, value36, value38, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (189 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 138 = true := by
  rw [value39, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (192 : Vertex) (208 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 8 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value8, value40, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (211 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 8 = false ∨ valuation q 43 = false ∨ valuation q 85 = false := by
  rw [value8, value40, value43, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 8 = false ∨ valuation q 44 = false ∨ valuation q 85 = false := by
  rw [value8, value40, value44, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (227 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 85 = false := by
  rw [value40, value43, value44, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (211 : Vertex) (227 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 47 = false ∨ valuation q 92 = false := by
  rw [value41, value42, value47, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (209 : Vertex) (240 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 140 = true ∨ valuation q 13 = true ∨ valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 92 = true := by
  rw [value13, value39, value41, value42, value92, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(80 : Vertex), (192 : Vertex), (209 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (240 : Vertex) [(80 : Vertex), (192 : Vertex), (209 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 141 = true ∨ valuation q 43 = true := by
  rw [value42, value43, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(211 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (208 : Vertex) [(211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 141 = true ∨ valuation q 41 = true := by
  rw [value41, value42, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(208 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (211 : Vertex) [(208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 142 = true ∨ valuation q 42 = true := by
  rw [value42, value43, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(209 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (195 : Vertex) [(209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 142 = true ∨ valuation q 40 = true := by
  rw [value40, value43, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(195 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (209 : Vertex) [(195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 24 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value24, value40, value44, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (163 : Vertex) (195 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E170.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112170
