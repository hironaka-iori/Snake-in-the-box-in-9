import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 14 = true := by
  rw [value1, value14]
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

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 33 = false ∨ valuation q 68 = false := by
  rw [value2, value5, value33, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (82 : Vertex) (194 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 130 = true ∨ valuation q 33 = true ∨ valuation q 68 = true := by
  rw [value2, value33, value68, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(194 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (82 : Vertex) [(194 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 38 = false ∨ valuation q 75 = false := by
  rw [value3, value9, value38, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (92 : Vertex) (204 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 131 = true ∨ valuation q 38 = true ∨ valuation q 75 = true := by
  rw [value3, value38, value75, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(204 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (92 : Vertex) [(204 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 131 = true ∨ valuation q 9 = true ∨ valuation q 75 = true := by
  rw [value3, value9, value75, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(92 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (204 : Vertex) [(92 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 132 = true ∨ valuation q 8 = true := by
  rw [value4, value8, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(88 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (82 : Vertex) [(88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 133 = true ∨ valuation q 4 = true ∨ valuation q 6 = true := by
  rw [value4, value5, value6, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(80 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (66 : Vertex) [(80 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 133 = true ∨ valuation q 2 = true ∨ valuation q 6 = true := by
  rw [value2, value5, value6, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(66 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (80 : Vertex) [(66 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 133 = true ∨ valuation q 2 = true ∨ valuation q 4 = true := by
  rw [value2, value4, value5, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(66 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (83 : Vertex) [(66 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 134 = true ∨ valuation q 7 = true := by
  rw [value6, value7, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (82 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 44 = false := by
  rw [value6, value7, value14, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (83 : Vertex) (119 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 80 = false := by
  rw [value6, value7, value14, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (83 : Vertex) (119 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 44 = false ∨ valuation q 80 = false := by
  rw [value7, value14, value44, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (119 : Vertex) (215 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 81 = false := by
  rw [value4, value8, value9, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (80 : Vertex) (92 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 136 = true ∨ valuation q 9 = true ∨ valuation q 81 = true := by
  rw [value8, value9, value81, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(92 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (80 : Vertex) [(92 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 136 = true ∨ valuation q 4 = true ∨ valuation q 81 = true := by
  rw [value4, value8, value81, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(80 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (92 : Vertex) [(80 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 136 = true ∨ valuation q 4 = true ∨ valuation q 9 = true := by
  rw [value4, value8, value9, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(80 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (344 : Vertex) [(80 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 10 = false := by
  rw [value3, value8, value9, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (76 : Vertex) (88 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 137 = true ∨ valuation q 3 = true ∨ valuation q 10 = true ∨ valuation q 11 = true := by
  rw [value3, value9, value10, value11, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(76 : Vertex), (93 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (88 : Vertex) [(76 : Vertex), (93 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 138 = true ∨ valuation q 48 = true := by
  rw [value10, value48, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(221 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (92 : Vertex) [(221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 138 = true ∨ valuation q 9 = true := by
  rw [value9, value10, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(92 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (221 : Vertex) [(92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 139 = true := by
  rw [value11, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (94 : Vertex) (92 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 140 = true := by
  rw [value12, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (103 : Vertex) (119 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 141 = true := by
  rw [value13, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (118 : Vertex) (119 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 7 = true ∨ valuation q 12 = true ∨ valuation q 13 = true := by
  rw [value7, value12, value13, value14, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (119 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(87 : Vertex), (103 : Vertex), (118 : Vertex)] := by decide
  have hg := other_cover q (119 : Vertex) (55 : Vertex) [(87 : Vertex), (103 : Vertex), (118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value15, value16, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 87 = false := by
  rw [value15, value16, value25, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 33 = false ∨ valuation q 87 = false := by
  rw [value15, value16, value33, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 143 = true ∨ valuation q 25 = true ∨ valuation q 33 = true ∨ valuation q 87 = true := by
  rw [value15, value25, value33, value87, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(146 : Vertex), (194 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (131 : Vertex) [(146 : Vertex), (194 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = false ∨ valuation q 20 = false ∨ valuation q 26 = false := by
  rw [value15, value16, value20, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (130 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E050.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112050
