import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 13 = true := by
  rw [value1, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ∈ [(119 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (55 : Vertex) [(119 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = true := by
  rw [value1]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 5 = true ∨ valuation q 33 = true ∨ valuation q 67 = true := by
  rw [value2, value5, value33, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ∈ [(82 : Vertex), (194 : Vertex), (322 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (66 : Vertex) [(82 : Vertex), (194 : Vertex), (322 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 33 = false ∨ valuation q 67 = false := by
  rw [value2, value5, value33, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (82 : Vertex) (194 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 129 = true ∨ valuation q 33 = true ∨ valuation q 67 = true := by
  rw [value2, value33, value67, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(194 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (82 : Vertex) [(194 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 129 = true ∨ valuation q 5 = true ∨ valuation q 33 = true := by
  rw [value2, value5, value33, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(82 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (322 : Vertex) [(82 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 38 = false ∨ valuation q 74 = false := by
  rw [value3, value9, value38, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (92 : Vertex) (204 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 130 = true ∨ valuation q 38 = true ∨ valuation q 74 = true := by
  rw [value3, value38, value74, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(204 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (92 : Vertex) [(204 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 130 = true ∨ valuation q 9 = true ∨ valuation q 74 = true := by
  rw [value3, value9, value74, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(92 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (204 : Vertex) [(92 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 130 = true ∨ valuation q 9 = true ∨ valuation q 38 = true := by
  rw [value3, value9, value38, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(92 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (332 : Vertex) [(92 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 131 = true ∨ valuation q 8 = true := by
  rw [value4, value8, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(88 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (82 : Vertex) [(88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 131 = true ∨ valuation q 5 = true := by
  rw [value4, value5, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(82 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (88 : Vertex) [(82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 6 = false := by
  rw [value2, value4, value5, value6]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (80 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 132 = true ∨ valuation q 4 = true ∨ valuation q 6 = true := by
  rw [value4, value5, value6, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(80 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (66 : Vertex) [(80 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 132 = true ∨ valuation q 2 = true ∨ valuation q 6 = true := by
  rw [value2, value5, value6, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(66 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (80 : Vertex) [(66 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 132 = true ∨ valuation q 2 = true ∨ valuation q 4 = true := by
  rw [value2, value4, value5, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(66 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (83 : Vertex) [(66 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 133 = true ∨ valuation q 7 = true := by
  rw [value6, value7, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (82 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 133 = true ∨ valuation q 5 = true := by
  rw [value5, value6, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(82 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (87 : Vertex) [(82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 44 = false := by
  rw [value6, value7, value13, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (83 : Vertex) (119 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 79 = false := by
  rw [value6, value7, value13, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (83 : Vertex) (119 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 79 = false := by
  rw [value7, value13, value44, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (119 : Vertex) (215 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 134 = true ∨ valuation q 6 = true ∨ valuation q 44 = true ∨ valuation q 79 = true := by
  rw [value6, value7, value44, value79, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(83 : Vertex), (215 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (119 : Vertex) [(83 : Vertex), (215 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 80 = false := by
  rw [value4, value8, value9, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (80 : Vertex) (92 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 9 = true ∨ valuation q 80 = true := by
  rw [value8, value9, value80, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(92 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (80 : Vertex) [(92 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 4 = true ∨ valuation q 80 = true := by
  rw [value4, value8, value80, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(80 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (92 : Vertex) [(80 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 3 = false ∨ valuation q 8 = false := by
  rw [value3, value8, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (92 : Vertex) (76 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 8 = true ∨ valuation q 10 = true := by
  rw [value8, value9, value10, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(88 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (76 : Vertex) [(88 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 3 = true ∨ valuation q 10 = true := by
  rw [value3, value9, value10, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(76 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (88 : Vertex) [(76 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 137 = true := by
  rw [value10, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (94 : Vertex) (92 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true := by
  rw [value11, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (103 : Vertex) (119 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true := by
  rw [value12, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (118 : Vertex) (119 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 140 = true ∨ valuation q 7 = true ∨ valuation q 11 = true ∨ valuation q 12 = true := by
  rw [value7, value11, value12, value13, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (119 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(87 : Vertex), (103 : Vertex), (118 : Vertex)] := by decide
  have hg := other_cover q (119 : Vertex) (55 : Vertex) [(87 : Vertex), (103 : Vertex), (118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E052.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112052
