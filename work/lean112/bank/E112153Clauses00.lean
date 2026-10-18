import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 125 = true := by
  rw [value1, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (2 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 126 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (6 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 49 = false := by
  rw [value3, value9, value15, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (69 : Vertex) (133 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 128 = true ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 50 = true := by
  rw [value4, value6, value16, value50, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(14 : Vertex), (134 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (2 : Vertex) [(14 : Vertex), (134 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 128 = true ∨ valuation q 2 = true ∨ valuation q 16 = true ∨ valuation q 50 = true := by
  rw [value2, value4, value16, value50, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(2 : Vertex), (134 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (14 : Vertex) [(2 : Vertex), (134 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 128 = true ∨ valuation q 2 = true ∨ valuation q 6 = true ∨ valuation q 16 = true := by
  rw [value2, value4, value6, value16, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(2 : Vertex), (14 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (262 : Vertex) [(2 : Vertex), (14 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 19 = false := by
  rw [value5, value6, value10, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (14 : Vertex) (76 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 54 = false := by
  rw [value5, value6, value10, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (14 : Vertex) (76 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 54 = false := by
  rw [value5, value10, value19, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (76 : Vertex) (140 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 5 = true := by
  rw [value5, value6, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(12 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (6 : Vertex) [(12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 4 = true := by
  rw [value4, value6, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (12 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 131 = true := by
  rw [value7, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (28 : Vertex) (12 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = true := by
  rw [value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ∈ [(69 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (65 : Vertex) [(69 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 8 = true := by
  rw [value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value3, value8, value9, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (65 : Vertex) (77 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 133 = true ∨ valuation q 3 = true ∨ valuation q 11 = true := by
  rw [value3, value9, value11, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(5 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (65 : Vertex) [(5 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 5 = true := by
  rw [value5, value10, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(12 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (77 : Vertex) [(12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 135 = true ∨ valuation q 10 = true := by
  rw [value10, value11, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(76 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (69 : Vertex) [(76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 15 = true := by
  rw [value12, value15, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(133 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (131 : Vertex) [(133 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 13 = true := by
  rw [value12, value13, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(131 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (133 : Vertex) [(131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true ∨ valuation q 18 = true := by
  rw [value13, value18, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (129 : Vertex) [(139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true ∨ valuation q 12 = true := by
  rw [value12, value13, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(129 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (139 : Vertex) [(129 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value14, value15, value16, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (134 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 22 = false := by
  rw [value14, value15, value16, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (134 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 84 = false := by
  rw [value14, value15, value22, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (148 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value3, value12, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (129 : Vertex) (132 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 20 = false := by
  rw [value3, value12, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (129 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 23 = false := by
  rw [value3, value12, value15, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (129 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value3, value14, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (132 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 3 = false ∨ valuation q 20 = false ∨ valuation q 23 = false := by
  rw [value3, value15, value20, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value12, value14, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (132 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value12, value14, value15, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (132 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E153.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112153
