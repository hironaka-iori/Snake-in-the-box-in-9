import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 139 = true ∨ valuation q 23 = true ∨ valuation q 32 = true ∨ valuation q 86 = true := by
  rw [value15, value23, value32, value86, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(149 : Vertex), (197 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (132 : Vertex) [(149 : Vertex), (197 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 139 = true ∨ valuation q 14 = true ∨ valuation q 32 = true ∨ valuation q 86 = true := by
  rw [value14, value15, value32, value86, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(132 : Vertex), (197 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (149 : Vertex) [(132 : Vertex), (197 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 139 = true ∨ valuation q 14 = true ∨ valuation q 23 = true ∨ valuation q 86 = true := by
  rw [value14, value15, value23, value86, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(132 : Vertex), (149 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (197 : Vertex) [(132 : Vertex), (149 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 139 = true ∨ valuation q 14 = true ∨ valuation q 23 = true ∨ valuation q 32 = true := by
  rw [value14, value15, value23, value32, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(132 : Vertex), (149 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (389 : Vertex) [(132 : Vertex), (149 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 35 = false := by
  rw [value16, value18, value27, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (139 : Vertex) (153 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 27 = true ∨ valuation q 35 = true ∨ valuation q 88 = true := by
  rw [value16, value27, value35, value88, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(153 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (139 : Vertex) [(153 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 18 = true ∨ valuation q 35 = true ∨ valuation q 88 = true := by
  rw [value16, value18, value35, value88, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(139 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (153 : Vertex) [(139 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 18 = true ∨ valuation q 27 = true ∨ valuation q 88 = true := by
  rw [value16, value18, value27, value88, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(139 : Vertex), (153 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (201 : Vertex) [(139 : Vertex), (153 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 18 = true ∨ valuation q 27 = true ∨ valuation q 35 = true := by
  rw [value16, value18, value27, value35, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(139 : Vertex), (153 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(139 : Vertex), (153 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 89 = false := by
  rw [value12, value17, value20, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (130 : Vertex) (142 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 12 = true ∨ valuation q 20 = true ∨ valuation q 89 = true := by
  rw [value12, value17, value20, value89, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(130 : Vertex), (142 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (139 : Vertex) [(130 : Vertex), (142 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value13, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 28 = false := by
  rw [value13, value16, value18, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 36 = false := by
  rw [value13, value16, value18, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 28 = false := by
  rw [value13, value17, value18, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 36 = false := by
  rw [value13, value17, value18, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value13, value18, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (155 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 28 = false := by
  rw [value16, value17, value18, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (138 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 36 = false := by
  rw [value16, value17, value18, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (138 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value16, value18, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (155 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value17, value18, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (155 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 143 = true ∨ valuation q 20 = true ∨ valuation q 90 = true := by
  rw [value19, value20, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(142 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (132 : Vertex) [(142 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 143 = true ∨ valuation q 14 = true ∨ valuation q 90 = true := by
  rw [value14, value19, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(132 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (142 : Vertex) [(132 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 143 = true ∨ valuation q 14 = true ∨ valuation q 20 = true := by
  rw [value14, value19, value20, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(132 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (396 : Vertex) [(132 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 20 = true := by
  rw [value20, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (142 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 92 = true := by
  rw [value17, value19, value20, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ∈ [(138 : Vertex), (140 : Vertex), (398 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (142 : Vertex) [(138 : Vertex), (140 : Vertex), (398 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 92 = false := by
  rw [value17, value19, value20, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (138 : Vertex) (140 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 17 = false ∨ valuation q 92 = false := by
  rw [value17, value92, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (142 : Vertex) (138 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 19 = false ∨ valuation q 92 = false := by
  rw [value19, value92, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (142 : Vertex) (140 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 144 = true ∨ valuation q 17 = true ∨ valuation q 92 = true := by
  rw [value17, value20, value92, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(138 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (140 : Vertex) [(138 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 94 = false := by
  rw [value21, value22, value26, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 22 = true ∨ valuation q 94 = true := by
  rw [value21, value22, value94, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(148 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (152 : Vertex) [(148 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E186.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112186
