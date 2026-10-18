import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 15 = false := by
  rw [value1, value2, value4, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (1 : Vertex) (8 : Vertex) (128 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 45 = false := by
  rw [value1, value2, value4, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (1 : Vertex) (8 : Vertex) (256 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 15 = false ∨ valuation q 45 = false := by
  rw [value1, value2, value15, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (1 : Vertex) (128 : Vertex) (256 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 15 = false ∨ valuation q 45 = false := by
  rw [value1, value4, value15, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (8 : Vertex) (128 : Vertex) (256 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 4 = true ∨ valuation q 15 = true ∨ valuation q 45 = true := by
  rw [value1, value4, value15, value45, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(8 : Vertex), (128 : Vertex), (256 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(8 : Vertex), (128 : Vertex), (256 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 2 = true ∨ valuation q 15 = true ∨ valuation q 45 = true := by
  rw [value1, value2, value15, value45, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(1 : Vertex), (128 : Vertex), (256 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (8 : Vertex) [(1 : Vertex), (128 : Vertex), (256 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 2 = true ∨ valuation q 4 = true ∨ valuation q 45 = true := by
  rw [value1, value2, value4, value45, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(1 : Vertex), (8 : Vertex), (256 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (128 : Vertex) [(1 : Vertex), (8 : Vertex), (256 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 2 = true ∨ valuation q 4 = true ∨ valuation q 15 = true := by
  rw [value1, value2, value4, value15, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (256 : Vertex) → w ∈ [(1 : Vertex), (8 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (256 : Vertex) [(1 : Vertex), (8 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true ∨ valuation q 8 = true ∨ valuation q 46 = true := by
  rw [value1, value2, value8, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (17 : Vertex), (257 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (1 : Vertex) [(0 : Vertex), (17 : Vertex), (257 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = false ∨ valuation q 8 = false ∨ valuation q 46 = false := by
  rw [value1, value2, value8, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (0 : Vertex) (17 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 1 = false ∨ valuation q 8 = false := by
  rw [value1, value8, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (1 : Vertex) (0 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 119 = true ∨ valuation q 8 = true ∨ valuation q 46 = true := by
  rw [value2, value8, value46, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(17 : Vertex), (257 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(17 : Vertex), (257 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 46 = true := by
  rw [value1, value2, value46, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex), (257 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex), (257 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 8 = true := by
  rw [value1, value2, value8, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(0 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (257 : Vertex) [(0 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 50 = false := by
  rw [value3, value11, value18, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (22 : Vertex) (134 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 120 = true ∨ valuation q 18 = true ∨ valuation q 50 = true := by
  rw [value3, value18, value50, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(134 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(134 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 4 = true := by
  rw [value4, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (8 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = true ∨ valuation q 20 = true ∨ valuation q 52 = true := by
  rw [value1, value4, value20, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (136 : Vertex), (264 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (8 : Vertex) [(0 : Vertex), (136 : Vertex), (264 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 20 = false ∨ valuation q 52 = false := by
  rw [value1, value4, value20, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (136 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 1 = false ∨ valuation q 20 = false := by
  rw [value1, value20, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (8 : Vertex) (0 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 20 = true ∨ valuation q 52 = true := by
  rw [value4, value20, value52, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(136 : Vertex), (264 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (0 : Vertex) [(136 : Vertex), (264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 52 = true := by
  rw [value1, value4, value52, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(0 : Vertex), (264 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (136 : Vertex) [(0 : Vertex), (264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 20 = true := by
  rw [value1, value4, value20, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(0 : Vertex), (136 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (264 : Vertex) [(0 : Vertex), (136 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = true ∨ valuation q 54 = true := by
  rw [value5, value7, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ∈ [(15 : Vertex), (267 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (11 : Vertex) [(15 : Vertex), (267 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 54 = true := by
  rw [value5, value54, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(267 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (15 : Vertex) [(267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 7 = true := by
  rw [value5, value7, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(15 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (267 : Vertex) [(15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 6 = true := by
  rw [value6, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (13 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 123 = true ∨ valuation q 13 = true := by
  rw [value6, value13, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (15 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 123 = true ∨ valuation q 7 = true := by
  rw [value6, value7, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(15 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (29 : Vertex) [(15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 57 = false := by
  rw [value5, value6, value7, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (11 : Vertex) (13 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 57 = true := by
  rw [value6, value7, value57, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(13 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (11 : Vertex) [(13 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 124 = true ∨ valuation q 5 = true ∨ valuation q 57 = true := by
  rw [value5, value7, value57, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(11 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (13 : Vertex) [(11 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E207.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112207
