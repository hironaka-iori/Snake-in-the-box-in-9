import E112149Semantics
import B112E149Inputs
namespace Snake9.Regrowth.E112149
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 34 = false := by
  rw [value18, value19, value20, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (168 : Vertex) (171 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 34 = false := by
  rw [value19, value20, value22, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (171 : Vertex) (174 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 119 = true ∨ valuation q 19 = true ∨ valuation q 28 = true ∨ valuation q 35 = true := by
  rw [value19, value20, value28, value35, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(170 : Vertex), (187 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (427 : Vertex) [(170 : Vertex), (187 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 22 = false := by
  rw [value15, value18, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (172 : Vertex) (164 : Vertex) (168 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 21 = true := by
  rw [value17, value19, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ∈ [(166 : Vertex), (170 : Vertex), (172 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (174 : Vertex) [(166 : Vertex), (170 : Vertex), (172 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 121 = true ∨ valuation q 19 = true ∨ valuation q 21 = true := by
  rw [value19, value21, value22, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(170 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (166 : Vertex) [(170 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 121 = true ∨ valuation q 17 = true ∨ valuation q 19 = true := by
  rw [value17, value19, value22, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(166 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (172 : Vertex) [(166 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 122 = true ∨ valuation q 16 = true ∨ valuation q 29 = true := by
  rw [value16, value23, value29, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(165 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (183 : Vertex) [(165 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 122 = true ∨ valuation q 16 = true ∨ valuation q 25 = true := by
  rw [value16, value23, value25, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(165 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (189 : Vertex) [(165 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 123 = true ∨ valuation q 17 = true := by
  rw [value17, value24, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(166 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (183 : Vertex) [(166 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 124 = true ∨ valuation q 24 = true ∨ valuation q 30 = true := by
  rw [value24, value25, value30, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(182 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (181 : Vertex) [(182 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 42 = false := by
  rw [value18, value26, value27, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (185 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 20 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value20, value27, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (171 : Vertex) (185 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 14 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value14, value31, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 130 = true ∨ valuation q 32 = true ∨ valuation q 34 = true := by
  rw [value31, value32, value34, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(227 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (162 : Vertex) [(227 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 131 = true ∨ valuation q 31 = true ∨ valuation q 35 = true := by
  rw [value31, value32, value35, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (243 : Vertex) [(226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 16 = true ∨ valuation q 36 = true := by
  rw [value16, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ∈ [(165 : Vertex), (237 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (229 : Vertex) [(165 : Vertex), (237 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 132 = true ∨ valuation q 36 = true := by
  rw [value33, value36, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(237 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (165 : Vertex) [(237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 132 = true ∨ valuation q 16 = true := by
  rw [value16, value33, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(165 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (237 : Vertex) [(165 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 133 = true ∨ valuation q 19 = true ∨ valuation q 31 = true ∨ valuation q 35 = true := by
  rw [value19, value31, value34, value35, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(170 : Vertex), (226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (106 : Vertex) [(170 : Vertex), (226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 20 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value20, value32, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 20 = false ∨ valuation q 32 = false ∨ valuation q 37 = false := by
  rw [value20, value32, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 20 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value20, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value32, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 135 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(239 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (229 : Vertex) [(239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 136 = true ∨ valuation q 35 = true ∨ valuation q 45 = true := by
  rw [value35, value37, value45, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(235 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (237 : Vertex) [(235 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value38, value39, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (241 : Vertex) (244 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 138 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(243 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (240 : Vertex) [(243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 138 = true ∨ valuation q 38 = true := by
  rw [value38, value39, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(240 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (243 : Vertex) [(240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 139 = true ∨ valuation q 32 = true := by
  rw [value32, value40, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (241 : Vertex) → w ∈ [(227 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (241 : Vertex) [(227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 38 = true ∨ valuation q 43 = true := by
  rw [value38, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ∈ [(240 : Vertex), (252 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (244 : Vertex) [(240 : Vertex), (252 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 140 = true ∨ valuation q 38 = true := by
  rw [value38, value41, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(240 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (252 : Vertex) [(240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E149.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112149
