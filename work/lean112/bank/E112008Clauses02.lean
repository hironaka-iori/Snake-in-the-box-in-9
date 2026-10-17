import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 18 = false ∨ valuation q 27 = false := by
  rw [value4, value13, value18, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (63 : Vertex) (119 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 27 = false ∨ valuation q 46 = false := by
  rw [value4, value13, value27, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (119 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 27 = false ∨ valuation q 81 = false := by
  rw [value4, value13, value27, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (119 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 27 = false := by
  rw [value11, value13, value18, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (63 : Vertex) (119 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 27 = false ∨ valuation q 46 = false := by
  rw [value11, value13, value27, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (119 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 27 = false ∨ valuation q 81 = false := by
  rw [value11, value13, value27, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (119 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 46 = false := by
  rw [value13, value18, value27, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (63 : Vertex) (119 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 81 = false := by
  rw [value13, value18, value27, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (63 : Vertex) (119 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 27 = false ∨ valuation q 46 = false ∨ valuation q 81 = false := by
  rw [value13, value27, value46, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (119 : Vertex) (183 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 16 = false := by
  rw [value9, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (56 : Vertex) (48 : Vertex) (58 : Vertex) (60 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 47 = false := by
  rw [value9, value14, value15, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (56 : Vertex) (48 : Vertex) (58 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 47 = false := by
  rw [value9, value14, value16, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (56 : Vertex) (48 : Vertex) (60 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 47 = true := by
  rw [value14, value15, value16, value47, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(58 : Vertex), (60 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (48 : Vertex) [(58 : Vertex), (60 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 17 = false := by
  rw [value6, value14, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (56 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 29 = false := by
  rw [value6, value14, value15, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (56 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 83 = false := by
  rw [value6, value14, value15, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (56 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 17 = false ∨ valuation q 29 = false := by
  rw [value6, value15, value17, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (62 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 17 = false ∨ valuation q 83 = false := by
  rw [value6, value15, value17, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (62 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 29 = false ∨ valuation q 83 = false := by
  rw [value6, value15, value29, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (122 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 29 = false := by
  rw [value14, value15, value17, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (56 : Vertex) (62 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 83 = false := by
  rw [value14, value15, value17, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (56 : Vertex) (62 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 29 = false ∨ valuation q 83 = false := by
  rw [value14, value15, value29, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (56 : Vertex) (122 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 29 = false ∨ valuation q 83 = false := by
  rw [value15, value17, value29, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (62 : Vertex) (122 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 17 = false := by
  rw [value12, value14, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (60 : Vertex) (52 : Vertex) (56 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 14 = true ∨ valuation q 17 = true := by
  rw [value14, value16, value17, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (60 : Vertex) w → w ∈ region → w ≠ (52 : Vertex) → w ∈ [(56 : Vertex), (62 : Vertex)] := by decide
  have hg := other_cover q (60 : Vertex) (52 : Vertex) [(56 : Vertex), (62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value15, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (58 : Vertex) (60 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 18 = true := by
  rw [value16, value17, value18, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(60 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (58 : Vertex) [(60 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value15, value17, value18, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (60 : Vertex) → w ∈ [(58 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (60 : Vertex) [(58 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 15 = true ∨ valuation q 16 = true := by
  rw [value15, value16, value17, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(58 : Vertex), (60 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (63 : Vertex) [(58 : Vertex), (60 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 17 = false := by
  rw [value8, value13, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (47 : Vertex) (55 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 51 = false := by
  rw [value8, value13, value18, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (47 : Vertex) (55 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 51 = false := by
  rw [value8, value17, value18, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (47 : Vertex) (62 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E008.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112008
