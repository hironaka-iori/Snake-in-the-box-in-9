import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 125 = true := by
  rw [value1, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (4 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 126 = true ∨ valuation q 1 = true ∨ valuation q 14 = true ∨ valuation q 32 = true := by
  rw [value1, value2, value14, value32, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(0 : Vertex), (68 : Vertex), (132 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (6 : Vertex) [(0 : Vertex), (68 : Vertex), (132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 126 = true ∨ valuation q 1 = true ∨ valuation q 3 = true ∨ valuation q 32 = true := by
  rw [value1, value2, value3, value32, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(0 : Vertex), (6 : Vertex), (132 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (68 : Vertex) [(0 : Vertex), (6 : Vertex), (132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 126 = true ∨ valuation q 1 = true ∨ valuation q 3 = true ∨ valuation q 14 = true := by
  rw [value1, value2, value3, value14, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(0 : Vertex), (6 : Vertex), (68 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (132 : Vertex) [(0 : Vertex), (6 : Vertex), (68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 127 = true ∨ valuation q 4 = true := by
  rw [value3, value4, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(7 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (4 : Vertex) [(7 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 127 = true ∨ valuation q 2 = true := by
  rw [value2, value3, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(4 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (7 : Vertex) [(4 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 15 = false := by
  rw [value3, value4, value8, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (7 : Vertex) (6 : Vertex) (23 : Vertex) (71 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 34 = false := by
  rw [value3, value4, value8, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (7 : Vertex) (6 : Vertex) (23 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 34 = false := by
  rw [value4, value8, value15, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (7 : Vertex) (23 : Vertex) (71 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 128 = true ∨ valuation q 8 = true ∨ valuation q 15 = true ∨ valuation q 34 = true := by
  rw [value4, value8, value15, value34, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(23 : Vertex), (71 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (6 : Vertex) [(23 : Vertex), (71 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 128 = true ∨ valuation q 3 = true ∨ valuation q 8 = true ∨ valuation q 34 = true := by
  rw [value3, value4, value8, value34, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(6 : Vertex), (23 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (71 : Vertex) [(6 : Vertex), (23 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 16 = false ∨ valuation q 35 = false := by
  rw [value5, value10, value16, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (25 : Vertex) (73 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 129 = true ∨ valuation q 16 = true ∨ valuation q 35 = true := by
  rw [value5, value16, value35, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (9 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(73 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (9 : Vertex) (25 : Vertex) [(73 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 24 = false := by
  rw [value6, value8, value11, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (23 : Vertex) (27 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 11 = true ∨ valuation q 24 = true := by
  rw [value6, value11, value24, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(27 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (23 : Vertex) [(27 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 8 = true ∨ valuation q 24 = true := by
  rw [value6, value8, value24, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(23 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (27 : Vertex) [(23 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = true := by
  rw [value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ∈ [(23 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (21 : Vertex) [(23 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 131 = true := by
  rw [value7, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (21 : Vertex) (23 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value4, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (7 : Vertex) (19 : Vertex) (21 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 6 = true ∨ valuation q 7 = true := by
  rw [value6, value7, value8, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(19 : Vertex), (21 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (7 : Vertex) [(19 : Vertex), (21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 4 = true ∨ valuation q 7 = true := by
  rw [value4, value7, value8, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(7 : Vertex), (21 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (19 : Vertex) [(7 : Vertex), (21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 10 = true := by
  rw [value9, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ∈ [(25 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (24 : Vertex) [(25 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 9 = true := by
  rw [value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 11 = false := by
  rw [value5, value9, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (25 : Vertex) (9 : Vertex) (24 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 5 = true ∨ valuation q 11 = true := by
  rw [value5, value10, value11, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(9 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (24 : Vertex) [(9 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 135 = true ∨ valuation q 6 = true := by
  rw [value6, value11, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(19 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (25 : Vertex) [(19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 22 = false := by
  rw [value12, value13, value16, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (67 : Vertex) (73 : Vertex) (81 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 16 = true ∨ valuation q 22 = true := by
  rw [value12, value16, value22, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(73 : Vertex), (81 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (67 : Vertex) [(73 : Vertex), (81 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 13 = true ∨ valuation q 22 = true := by
  rw [value12, value13, value22, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(67 : Vertex), (81 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (73 : Vertex) [(67 : Vertex), (81 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 13 = true ∨ valuation q 16 = true := by
  rw [value12, value13, value16, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(67 : Vertex), (73 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (81 : Vertex) [(67 : Vertex), (73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 13 = true := by
  rw [value13, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (67 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 24 = true := by
  rw [value12, value13, value15, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ∈ [(65 : Vertex), (71 : Vertex), (83 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (67 : Vertex) [(65 : Vertex), (71 : Vertex), (83 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E105.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112105
