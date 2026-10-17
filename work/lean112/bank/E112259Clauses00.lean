import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 54 = false := by
  rw [value1, value3, value5, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (4 : Vertex) (8 : Vertex) (128 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 5 = true ∨ valuation q 54 = true := by
  rw [value1, value5, value54, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(8 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (4 : Vertex) [(8 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 3 = true ∨ valuation q 54 = true := by
  rw [value1, value3, value54, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(4 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (8 : Vertex) [(4 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 3 = true ∨ valuation q 5 = true := by
  rw [value1, value3, value5, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(4 : Vertex), (8 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (128 : Vertex) [(4 : Vertex), (8 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 20 = false ∨ valuation q 56 = false := by
  rw [value2, value4, value20, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (7 : Vertex) (35 : Vertex) (131 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 20 = true ∨ valuation q 56 = true := by
  rw [value2, value20, value56, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(35 : Vertex), (131 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (7 : Vertex) [(35 : Vertex), (131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 4 = true ∨ valuation q 56 = true := by
  rw [value2, value4, value56, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(7 : Vertex), (131 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (35 : Vertex) [(7 : Vertex), (131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 4 = true ∨ valuation q 20 = true := by
  rw [value2, value4, value20, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(7 : Vertex), (35 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (131 : Vertex) [(7 : Vertex), (35 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 21 = false ∨ valuation q 57 = false := by
  rw [value1, value3, value21, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (4 : Vertex) (0 : Vertex) (36 : Vertex) (132 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 21 = true ∨ valuation q 57 = true := by
  rw [value3, value21, value57, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(36 : Vertex), (132 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (0 : Vertex) [(36 : Vertex), (132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 57 = true := by
  rw [value1, value3, value57, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(0 : Vertex), (132 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (36 : Vertex) [(0 : Vertex), (132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 21 = true := by
  rw [value1, value3, value21, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(0 : Vertex), (36 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (132 : Vertex) [(0 : Vertex), (36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = true := by
  rw [value2, value4]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ∈ [(3 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (7 : Vertex) [(3 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 120 = true := by
  rw [value4, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (7 : Vertex) (3 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value1, value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (10 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 14 = false := by
  rw [value1, value5, value6, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 23 = false := by
  rw [value1, value5, value6, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 60 = false := by
  rw [value1, value5, value6, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 14 = false := by
  rw [value1, value5, value7, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 23 = false := by
  rw [value1, value5, value7, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 60 = false := by
  rw [value1, value5, value7, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value1, value5, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (24 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 60 = false := by
  rw [value1, value5, value14, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (24 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 23 = false ∨ valuation q 60 = false := by
  rw [value1, value5, value23, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (40 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 14 = false := by
  rw [value5, value6, value7, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (10 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 23 = false := by
  rw [value5, value6, value7, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (10 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 60 = false := by
  rw [value5, value6, value7, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (10 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value5, value6, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (24 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 60 = false := by
  rw [value5, value6, value14, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (24 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 60 = false := by
  rw [value5, value6, value23, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (40 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value5, value7, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (10 : Vertex) (24 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 60 = false := by
  rw [value5, value7, value14, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (10 : Vertex) (24 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E259.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112259
