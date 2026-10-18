import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 5 = false ∨ valuation q 25 = false ∨ valuation q 43 = false := by
  rw [value5, value8, value25, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (72 : Vertex) (108 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 25 = true ∨ valuation q 43 = true := by
  rw [value8, value25, value43, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(108 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (72 : Vertex) [(108 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 5 = true ∨ valuation q 43 = true := by
  rw [value5, value8, value43, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(72 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (108 : Vertex) [(72 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 5 = true ∨ valuation q 25 = true := by
  rw [value5, value8, value25, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(72 : Vertex), (108 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (204 : Vertex) [(72 : Vertex), (108 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = false ∨ valuation q 18 = false ∨ valuation q 44 = false := by
  rw [value7, value9, value18, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (75 : Vertex) (95 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 18 = true ∨ valuation q 44 = true := by
  rw [value9, value18, value44, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(95 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (75 : Vertex) [(95 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 7 = true ∨ valuation q 44 = true := by
  rw [value7, value9, value44, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(75 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (95 : Vertex) [(75 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 7 = true ∨ valuation q 18 = true := by
  rw [value7, value9, value18, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(75 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (207 : Vertex) [(75 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 10 = true := by
  rw [value10, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (80 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 27 = false ∨ valuation q 82 = false := by
  rw [value10, value12, value27, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (84 : Vertex) (112 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 27 = false ∨ valuation q 82 = false := by
  rw [value27, value82, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (80 : Vertex) (112 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 137 = true ∨ valuation q 12 = true ∨ valuation q 27 = true := by
  rw [value10, value12, value27, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(84 : Vertex), (112 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (336 : Vertex) [(84 : Vertex), (112 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 11 = true := by
  rw [value11, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (83 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = true ∨ valuation q 29 = true ∨ valuation q 46 = true := by
  rw [value11, value13, value29, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ∈ [(87 : Vertex), (115 : Vertex), (211 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (83 : Vertex) [(87 : Vertex), (115 : Vertex), (211 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 29 = true ∨ valuation q 46 = true := by
  rw [value11, value29, value46, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(115 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (87 : Vertex) [(115 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 13 = true ∨ valuation q 46 = true := by
  rw [value11, value13, value46, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(87 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (115 : Vertex) [(87 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 13 = true ∨ valuation q 29 = true := by
  rw [value11, value13, value29, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(87 : Vertex), (115 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (211 : Vertex) [(87 : Vertex), (115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 30 = false ∨ valuation q 47 = false := by
  rw [value10, value12, value30, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (80 : Vertex) (116 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true ∨ valuation q 30 = true ∨ valuation q 47 = true := by
  rw [value12, value30, value47, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(116 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(116 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true ∨ valuation q 10 = true ∨ valuation q 47 = true := by
  rw [value10, value12, value47, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(80 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (116 : Vertex) [(80 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true ∨ valuation q 10 = true ∨ valuation q 30 = true := by
  rw [value10, value12, value30, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(80 : Vertex), (116 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (212 : Vertex) [(80 : Vertex), (116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 49 = false := by
  rw [value11, value13, value18, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (83 : Vertex) (95 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 140 = true ∨ valuation q 18 = true ∨ valuation q 49 = true := by
  rw [value13, value18, value49, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(95 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (83 : Vertex) [(95 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 140 = true ∨ valuation q 11 = true ∨ valuation q 18 = true := by
  rw [value11, value13, value18, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(83 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (215 : Vertex) [(83 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 14 = true := by
  rw [value14, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (89 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 50 = true ∨ valuation q 87 = true := by
  rw [value6, value14, value16, value50, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ∈ [(73 : Vertex), (93 : Vertex), (217 : Vertex), (345 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (89 : Vertex) [(73 : Vertex), (93 : Vertex), (217 : Vertex), (345 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 16 = false ∨ valuation q 50 = false := by
  rw [value16, value50, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (89 : Vertex) (93 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 50 = false ∨ valuation q 87 = false := by
  rw [value50, value87, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (89 : Vertex) (217 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 50 = true ∨ valuation q 87 = true := by
  rw [value14, value16, value50, value87, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(93 : Vertex), (217 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (73 : Vertex) [(93 : Vertex), (217 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 6 = true ∨ valuation q 50 = true ∨ valuation q 87 = true := by
  rw [value6, value14, value50, value87, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(73 : Vertex), (217 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (93 : Vertex) [(73 : Vertex), (217 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 87 = true := by
  rw [value6, value14, value16, value87, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(73 : Vertex), (93 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (217 : Vertex) [(73 : Vertex), (93 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 50 = true := by
  rw [value6, value14, value16, value50, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(73 : Vertex), (93 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (345 : Vertex) [(73 : Vertex), (93 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E256.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112256
