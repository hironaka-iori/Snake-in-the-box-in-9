import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value14, value15, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 25 = false ∨ valuation q 86 = false := by
  rw [value14, value15, value25, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 33 = false ∨ valuation q 86 = false := by
  rw [value14, value15, value33, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 33 = false ∨ valuation q 86 = false := by
  rw [value14, value25, value33, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (146 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 25 = true ∨ valuation q 33 = true ∨ valuation q 86 = true := by
  rw [value14, value25, value33, value86, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(146 : Vertex), (194 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (131 : Vertex) [(146 : Vertex), (194 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 15 = true ∨ valuation q 33 = true ∨ valuation q 86 = true := by
  rw [value14, value15, value33, value86, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(131 : Vertex), (194 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (146 : Vertex) [(131 : Vertex), (194 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 15 = true ∨ valuation q 25 = true ∨ valuation q 86 = true := by
  rw [value14, value15, value25, value86, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(131 : Vertex), (146 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (194 : Vertex) [(131 : Vertex), (146 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 15 = true ∨ valuation q 25 = true ∨ valuation q 33 = true := by
  rw [value14, value15, value25, value33, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(131 : Vertex), (146 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (386 : Vertex) [(131 : Vertex), (146 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 26 = false := by
  rw [value14, value15, value19, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (130 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 19 = true ∨ valuation q 26 = true := by
  rw [value15, value19, value26, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(139 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(139 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 14 = true ∨ valuation q 26 = true := by
  rw [value14, value15, value26, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(130 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (139 : Vertex) [(130 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 14 = true ∨ valuation q 19 = true := by
  rw [value14, value15, value19, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(130 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (147 : Vertex) [(130 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 16 = true := by
  rw [value16, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (132 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 87 = false := by
  rw [value16, value17, value20, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 17 = false ∨ valuation q 87 = false := by
  rw [value17, value87, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (132 : Vertex) (133 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 20 = true ∨ valuation q 87 = true := by
  rw [value16, value20, value87, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(140 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (133 : Vertex) [(140 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 17 = true ∨ valuation q 87 = true := by
  rw [value16, value17, value87, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(133 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (140 : Vertex) [(133 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 21 = true ∨ valuation q 88 = true := by
  rw [value17, value21, value88, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(141 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (132 : Vertex) [(141 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 16 = true ∨ valuation q 88 = true := by
  rw [value16, value17, value88, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(132 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (141 : Vertex) [(132 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 16 = true ∨ valuation q 21 = true := by
  rw [value16, value17, value21, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(132 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (389 : Vertex) [(132 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 92 = false := by
  rw [value18, value19, value21, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (139 : Vertex) (141 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 21 = true ∨ valuation q 92 = true := by
  rw [value18, value21, value92, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(141 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (139 : Vertex) [(141 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 19 = true ∨ valuation q 92 = true := by
  rw [value18, value19, value92, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(139 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (141 : Vertex) [(139 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 19 = true ∨ valuation q 21 = true := by
  rw [value18, value19, value21, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 19 = true := by
  rw [value19, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (139 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 94 = true := by
  rw [value15, value18, value19, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ∈ [(131 : Vertex), (137 : Vertex), (395 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (139 : Vertex) [(131 : Vertex), (137 : Vertex), (395 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 94 = false := by
  rw [value15, value18, value19, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 18 = true ∨ valuation q 94 = true := by
  rw [value18, value19, value94, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(137 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (131 : Vertex) [(137 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 15 = true ∨ valuation q 94 = true := by
  rw [value15, value19, value94, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(131 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (137 : Vertex) [(131 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 16 = false ∨ valuation q 22 = false ∨ valuation q 29 = false := by
  rw [value16, value20, value22, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (132 : Vertex) (142 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 16 = false ∨ valuation q 22 = false ∨ valuation q 38 = false := by
  rw [value16, value20, value22, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (132 : Vertex) (142 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 16 = false ∨ valuation q 29 = false ∨ valuation q 38 = false := by
  rw [value16, value20, value29, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (132 : Vertex) (156 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E052.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112052
