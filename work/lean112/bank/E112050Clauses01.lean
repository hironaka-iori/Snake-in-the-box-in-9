import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 20 = true ∨ valuation q 26 = true := by
  rw [value16, value20, value26, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(139 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(139 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 26 = true := by
  rw [value15, value16, value26, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(130 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (139 : Vertex) [(130 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 20 = true := by
  rw [value15, value16, value20, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(130 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (147 : Vertex) [(130 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 88 = false := by
  rw [value17, value18, value21, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value18, value21, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 18 = false ∨ valuation q 88 = false := by
  rw [value18, value88, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (132 : Vertex) (133 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 145 = true ∨ valuation q 21 = true ∨ valuation q 88 = true := by
  rw [value17, value21, value88, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(140 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (133 : Vertex) [(140 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 22 = true ∨ valuation q 89 = true := by
  rw [value18, value22, value89, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(141 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (132 : Vertex) [(141 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 17 = true ∨ valuation q 89 = true := by
  rw [value17, value18, value89, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(132 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (141 : Vertex) [(132 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 17 = true ∨ valuation q 22 = true := by
  rw [value17, value18, value22, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(132 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (389 : Vertex) [(132 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 93 = false := by
  rw [value19, value20, value22, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (139 : Vertex) (141 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 22 = true ∨ valuation q 93 = true := by
  rw [value19, value22, value93, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(141 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (139 : Vertex) [(141 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 20 = true ∨ valuation q 93 = true := by
  rw [value19, value20, value93, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(139 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (141 : Vertex) [(139 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 20 = true ∨ valuation q 22 = true := by
  rw [value19, value20, value22, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 20 = true := by
  rw [value20, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (139 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 95 = true := by
  rw [value16, value19, value20, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ∈ [(131 : Vertex), (137 : Vertex), (395 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (139 : Vertex) [(131 : Vertex), (137 : Vertex), (395 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 95 = false := by
  rw [value16, value19, value20, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 19 = true ∨ valuation q 95 = true := by
  rw [value19, value20, value95, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(137 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (131 : Vertex) [(137 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 16 = true ∨ valuation q 95 = true := by
  rw [value16, value20, value95, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(131 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (137 : Vertex) [(131 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value16, value19, value20, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (395 : Vertex) → w ∈ [(131 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (395 : Vertex) [(131 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 17 = false ∨ valuation q 29 = false ∨ valuation q 38 = false := by
  rw [value17, value21, value29, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (132 : Vertex) (156 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 29 = false ∨ valuation q 38 = false := by
  rw [value21, value22, value29, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (141 : Vertex) (156 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 21 = false := by
  rw [value18, value19, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 96 = false := by
  rw [value18, value19, value22, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 96 = false := by
  rw [value18, value21, value22, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (140 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 96 = false := by
  rw [value19, value21, value22, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (137 : Vertex) (140 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 150 = true ∨ valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 96 = true := by
  rw [value19, value21, value22, value96, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(137 : Vertex), (140 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (133 : Vertex) [(137 : Vertex), (140 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 150 = true ∨ valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 21 = true := by
  rw [value18, value19, value21, value22, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(133 : Vertex), (137 : Vertex), (140 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (397 : Vertex) [(133 : Vertex), (137 : Vertex), (140 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 97 = false := by
  rw [value21, value23, value30, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (140 : Vertex) (158 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 30 = false ∨ valuation q 39 = false ∨ valuation q 97 = false := by
  rw [value23, value30, value39, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (158 : Vertex) (206 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 151 = true ∨ valuation q 21 = true ∨ valuation q 39 = true ∨ valuation q 97 = true := by
  rw [value21, value23, value39, value97, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(140 : Vertex), (206 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (158 : Vertex) [(140 : Vertex), (206 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 152 = true ∨ valuation q 28 = true := by
  rw [value24, value28, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(152 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (146 : Vertex) [(152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E050.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112050
