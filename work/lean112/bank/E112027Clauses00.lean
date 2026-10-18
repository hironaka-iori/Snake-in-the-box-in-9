import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 15 = false := by
  rw [value1, value2, value3, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (1 : Vertex) (2 : Vertex) (128 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 119 = true ∨ valuation q 3 = true ∨ valuation q 15 = true := by
  rw [value1, value3, value15, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(2 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(2 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 9 = false := by
  rw [value1, value2, value5, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (0 : Vertex) (17 : Vertex) (65 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 120 = true ∨ valuation q 5 = true ∨ valuation q 9 = true := by
  rw [value2, value5, value9, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(17 : Vertex), (65 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(17 : Vertex), (65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 120 = true ∨ valuation q 1 = true ∨ valuation q 9 = true := by
  rw [value1, value2, value9, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex), (65 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex), (65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 120 = true ∨ valuation q 1 = true ∨ valuation q 5 = true := by
  rw [value1, value2, value5, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(0 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (65 : Vertex) [(0 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 6 = false := by
  rw [value1, value3, value4, value6]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (0 : Vertex) (6 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 16 = false := by
  rw [value1, value3, value4, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (0 : Vertex) (6 : Vertex) (130 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 51 = false := by
  rw [value1, value3, value4, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (0 : Vertex) (6 : Vertex) (258 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 16 = false := by
  rw [value1, value3, value6, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (0 : Vertex) (18 : Vertex) (130 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 51 = false := by
  rw [value1, value3, value6, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (0 : Vertex) (18 : Vertex) (258 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 51 = false := by
  rw [value1, value3, value16, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (0 : Vertex) (130 : Vertex) (258 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 16 = false := by
  rw [value3, value4, value6, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (6 : Vertex) (18 : Vertex) (130 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 51 = false := by
  rw [value3, value4, value6, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (6 : Vertex) (18 : Vertex) (258 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 51 = false := by
  rw [value3, value6, value10, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (18 : Vertex) (66 : Vertex) (258 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 16 = false ∨ valuation q 51 = false := by
  rw [value3, value6, value16, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (18 : Vertex) (130 : Vertex) (258 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 1 = false ∨ valuation q 6 = false := by
  rw [value1, value6, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (2 : Vertex) (0 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 1 = false ∨ valuation q 16 = false := by
  rw [value1, value16, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (2 : Vertex) (0 : Vertex) (130 : Vertex) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 4 = true ∨ valuation q 6 = true ∨ valuation q 10 = true ∨ valuation q 16 = true ∨ valuation q 51 = true := by
  rw [value3, value4, value6, value10, value16, value51, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(6 : Vertex), (18 : Vertex), (66 : Vertex), (130 : Vertex), (258 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (0 : Vertex) [(6 : Vertex), (18 : Vertex), (66 : Vertex), (130 : Vertex), (258 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 10 = true ∨ valuation q 16 = true ∨ valuation q 51 = true := by
  rw [value1, value3, value4, value10, value16, value51, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(0 : Vertex), (6 : Vertex), (66 : Vertex), (130 : Vertex), (258 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (18 : Vertex) [(0 : Vertex), (6 : Vertex), (66 : Vertex), (130 : Vertex), (258 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value3, value4, value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (2 : Vertex) (22 : Vertex) (70 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 55 = false := by
  rw [value3, value4, value8, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (2 : Vertex) (22 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 19 = false := by
  rw [value3, value4, value11, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (2 : Vertex) (70 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 55 = false := by
  rw [value3, value4, value11, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (2 : Vertex) (70 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 19 = false ∨ valuation q 55 = false := by
  rw [value3, value4, value19, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (2 : Vertex) (134 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 19 = false := by
  rw [value4, value8, value11, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (22 : Vertex) (70 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 55 = false := by
  rw [value4, value8, value11, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (22 : Vertex) (70 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 122 = true ∨ valuation q 8 = true ∨ valuation q 11 = true ∨ valuation q 19 = true ∨ valuation q 55 = true := by
  rw [value4, value8, value11, value19, value55, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(22 : Vertex), (70 : Vertex), (134 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (2 : Vertex) [(22 : Vertex), (70 : Vertex), (134 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 7 = true := by
  rw [value5, value7, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(19 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (1 : Vertex) [(19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 2 = true := by
  rw [value2, value5, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(1 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (19 : Vertex) [(1 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value3, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 7 = true ∨ valuation q 8 = true := by
  rw [value6, value7, value8, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(19 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (2 : Vertex) [(19 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E027.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112027
