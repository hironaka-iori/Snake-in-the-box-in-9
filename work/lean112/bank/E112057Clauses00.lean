import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 5 = false := by
  rw [value1, value2, value3, value5]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (1 : Vertex) (2 : Vertex) (8 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 128 = true ∨ valuation q 3 = true ∨ valuation q 5 = true := by
  rw [value1, value3, value5, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(2 : Vertex), (8 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(2 : Vertex), (8 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 128 = true ∨ valuation q 2 = true ∨ valuation q 5 = true := by
  rw [value1, value2, value5, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(1 : Vertex), (8 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (2 : Vertex) [(1 : Vertex), (8 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 128 = true ∨ valuation q 2 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(1 : Vertex), (2 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (8 : Vertex) [(1 : Vertex), (2 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 2 = true := by
  rw [value2, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (1 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 10 = true := by
  rw [value1, value2, value4, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (5 : Vertex), (17 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (1 : Vertex) [(0 : Vertex), (5 : Vertex), (17 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 10 = false := by
  rw [value1, value2, value4, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (0 : Vertex) (5 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 1 = false ∨ valuation q 4 = false := by
  rw [value1, value4, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (1 : Vertex) (0 : Vertex) (5 : Vertex) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 1 = false ∨ valuation q 10 = false := by
  rw [value1, value10, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (1 : Vertex) (0 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 129 = true ∨ valuation q 4 = true ∨ valuation q 10 = true := by
  rw [value2, value4, value10, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(5 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(5 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 129 = true ∨ valuation q 1 = true ∨ valuation q 10 = true := by
  rw [value1, value2, value10, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(0 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (5 : Vertex) [(0 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 129 = true ∨ valuation q 1 = true ∨ valuation q 4 = true := by
  rw [value1, value2, value4, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex), (5 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex), (5 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = true ∨ valuation q 6 = true ∨ valuation q 11 = true := by
  rw [value1, value3, value6, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (10 : Vertex), (18 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (2 : Vertex) [(0 : Vertex), (10 : Vertex), (18 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 11 = false := by
  rw [value1, value3, value6, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (0 : Vertex) (10 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 1 = false ∨ valuation q 11 = false := by
  rw [value1, value11, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (2 : Vertex) (0 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 130 = true ∨ valuation q 6 = true ∨ valuation q 11 = true := by
  rw [value3, value6, value11, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(10 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (0 : Vertex) [(10 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 130 = true ∨ valuation q 1 = true ∨ valuation q 11 = true := by
  rw [value1, value3, value11, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(0 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (10 : Vertex) [(0 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 23 = false := by
  rw [value2, value4, value13, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (21 : Vertex) (69 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 40 = false := by
  rw [value2, value4, value13, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (21 : Vertex) (133 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 70 = false := by
  rw [value2, value4, value13, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (21 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 23 = false ∨ valuation q 40 = false := by
  rw [value2, value4, value23, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (69 : Vertex) (133 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 23 = false ∨ valuation q 70 = false := by
  rw [value2, value4, value23, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (69 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 40 = false ∨ valuation q 70 = false := by
  rw [value2, value4, value40, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (133 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 40 = false := by
  rw [value4, value13, value23, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (21 : Vertex) (69 : Vertex) (133 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 40 = false ∨ valuation q 70 = false := by
  rw [value4, value13, value40, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (21 : Vertex) (133 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 131 = true ∨ valuation q 13 = true ∨ valuation q 23 = true ∨ valuation q 40 = true ∨ valuation q 70 = true := by
  rw [value4, value13, value23, value40, value70, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(21 : Vertex), (69 : Vertex), (133 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (1 : Vertex) [(21 : Vertex), (69 : Vertex), (133 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 131 = true ∨ valuation q 2 = true ∨ valuation q 23 = true ∨ valuation q 40 = true ∨ valuation q 70 = true := by
  rw [value2, value4, value23, value40, value70, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(1 : Vertex), (69 : Vertex), (133 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (21 : Vertex) [(1 : Vertex), (69 : Vertex), (133 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 131 = true ∨ valuation q 2 = true ∨ valuation q 13 = true ∨ valuation q 23 = true ∨ valuation q 40 = true := by
  rw [value2, value4, value13, value23, value40, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(1 : Vertex), (21 : Vertex), (69 : Vertex), (133 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (261 : Vertex) [(1 : Vertex), (21 : Vertex), (69 : Vertex), (133 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 5 = true := by
  rw [value5, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (8 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value1, value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (12 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 26 = false := by
  rw [value1, value5, value6, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 43 = false := by
  rw [value1, value5, value6, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E057.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112057
