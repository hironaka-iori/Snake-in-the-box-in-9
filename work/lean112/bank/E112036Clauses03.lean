import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 158 = true ∨ valuation q 17 = true ∨ valuation q 26 = true ∨ valuation q 27 = true := by
  rw [value17, value26, value27, value30, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(62 : Vertex), (118 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (124 : Vertex) [(62 : Vertex), (118 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = true ∨ valuation q 33 = true ∨ valuation q 37 = true ∨ valuation q 41 = true ∨ valuation q 88 = true := by
  rw [value31, value32, value33, value37, value41, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ∈ [(161 : Vertex), (162 : Vertex), (168 : Vertex), (176 : Vertex), (416 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (160 : Vertex) [(161 : Vertex), (162 : Vertex), (168 : Vertex), (176 : Vertex), (416 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value31, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 41 = false := by
  rw [value31, value32, value33, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 88 = false := by
  rw [value31, value32, value33, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value31, value32, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 88 = false := by
  rw [value31, value32, value37, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 41 = false ∨ valuation q 88 = false := by
  rw [value31, value32, value41, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value31, value33, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 88 = false := by
  rw [value31, value33, value37, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 41 = false ∨ valuation q 88 = false := by
  rw [value31, value33, value41, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 88 = false := by
  rw [value31, value37, value41, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 159 = true ∨ valuation q 32 = true ∨ valuation q 33 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value31, value32, value33, value37, value41, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(161 : Vertex), (162 : Vertex), (168 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (416 : Vertex) [(161 : Vertex), (162 : Vertex), (168 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value31, value32, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (163 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value31, value32, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value32, value34, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (163 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 89 = true := by
  rw [value32, value34, value35, value42, value89, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(163 : Vertex), (165 : Vertex), (177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(163 : Vertex), (165 : Vertex), (177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 89 = true := by
  rw [value31, value32, value35, value42, value89, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(160 : Vertex), (165 : Vertex), (177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (163 : Vertex) [(160 : Vertex), (165 : Vertex), (177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 42 = true ∨ valuation q 89 = true := by
  rw [value31, value32, value34, value42, value89, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (165 : Vertex) [(160 : Vertex), (163 : Vertex), (177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 89 = true := by
  rw [value31, value32, value34, value35, value89, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (165 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (177 : Vertex) [(160 : Vertex), (163 : Vertex), (165 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 42 = true := by
  rw [value31, value32, value34, value35, value42, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (165 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (417 : Vertex) [(160 : Vertex), (163 : Vertex), (165 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 31 = false ∨ valuation q 36 = false := by
  rw [value1, value31, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (160 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 31 = false ∨ valuation q 43 = false := by
  rw [value1, value31, value33, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (160 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value1, value33, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (163 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 34 = false ∨ valuation q 43 = false := by
  rw [value1, value33, value34, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (163 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 36 = false ∨ valuation q 51 = false := by
  rw [value1, value33, value36, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (166 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 43 = false ∨ valuation q 51 = false := by
  rw [value1, value33, value43, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (34 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value31, value33, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 43 = false := by
  rw [value31, value33, value34, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 51 = false := by
  rw [value31, value33, value36, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (166 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value2, value32, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (162 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 32 = false ∨ valuation q 38 = false := by
  rw [value2, value32, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E036.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112036
