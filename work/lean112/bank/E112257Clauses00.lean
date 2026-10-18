import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 36 = false := by
  rw [value1, value3, value10, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (4 : Vertex) (16 : Vertex) (128 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 10 = true ∨ valuation q 36 = true := by
  rw [value1, value10, value36, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(16 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (4 : Vertex) [(16 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 3 = true ∨ valuation q 36 = true := by
  rw [value1, value3, value36, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(4 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (16 : Vertex) [(4 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 3 = true ∨ valuation q 10 = true := by
  rw [value1, value3, value10, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(4 : Vertex), (16 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (128 : Vertex) [(4 : Vertex), (16 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 20 = false ∨ valuation q 37 = false := by
  rw [value2, value5, value20, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (7 : Vertex) (35 : Vertex) (131 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 20 = true ∨ valuation q 37 = true := by
  rw [value2, value20, value37, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(35 : Vertex), (131 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (7 : Vertex) [(35 : Vertex), (131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 5 = true ∨ valuation q 37 = true := by
  rw [value2, value5, value37, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(7 : Vertex), (131 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (35 : Vertex) [(7 : Vertex), (131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 5 = true ∨ valuation q 20 = true := by
  rw [value2, value5, value20, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(7 : Vertex), (35 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (131 : Vertex) [(7 : Vertex), (35 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 21 = false := by
  rw [value1, value3, value4, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (4 : Vertex) (0 : Vertex) (6 : Vertex) (36 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 4 = true ∨ valuation q 21 = true := by
  rw [value3, value4, value21, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(6 : Vertex), (36 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (0 : Vertex) [(6 : Vertex), (36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 21 = true := by
  rw [value1, value3, value21, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(0 : Vertex), (36 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (6 : Vertex) [(0 : Vertex), (36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 4 = true := by
  rw [value1, value3, value4, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(0 : Vertex), (6 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (36 : Vertex) [(0 : Vertex), (6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 9 = false := by
  rw [value3, value4, value5, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (7 : Vertex) (14 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 14 = false := by
  rw [value3, value4, value5, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (7 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 22 = false := by
  rw [value3, value4, value5, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (7 : Vertex) (38 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 39 = false := by
  rw [value3, value4, value5, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (7 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 14 = false := by
  rw [value3, value4, value9, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (14 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 22 = false := by
  rw [value3, value4, value9, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (14 : Vertex) (38 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 39 = false := by
  rw [value3, value4, value9, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (14 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 22 = false := by
  rw [value3, value4, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (22 : Vertex) (38 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 39 = false := by
  rw [value3, value4, value14, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (22 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 14 = false := by
  rw [value4, value5, value9, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (7 : Vertex) (14 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 22 = false := by
  rw [value4, value5, value9, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (7 : Vertex) (14 : Vertex) (38 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 39 = false := by
  rw [value4, value5, value9, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (7 : Vertex) (14 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 22 = false := by
  rw [value4, value5, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (7 : Vertex) (22 : Vertex) (38 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 40 = false := by
  rw [value2, value4, value5, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (7 : Vertex) (3 : Vertex) (6 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 2 = false ∨ valuation q 40 = false := by
  rw [value2, value40, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (7 : Vertex) (3 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 4 = true ∨ valuation q 40 = true := by
  rw [value4, value5, value40, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(6 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (3 : Vertex) [(6 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 2 = true ∨ valuation q 4 = true := by
  rw [value2, value4, value5, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(3 : Vertex), (6 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (135 : Vertex) [(3 : Vertex), (6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 24 = true := by
  rw [value6, value24, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (9 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(41 : Vertex)] := by decide
  have hg := other_cover q (9 : Vertex) (13 : Vertex) [(41 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 8 = true := by
  rw [value6, value8, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (9 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(13 : Vertex)] := by decide
  have hg := other_cover q (9 : Vertex) (41 : Vertex) [(13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 25 = true ∨ valuation q 41 = true := by
  rw [value7, value25, value41, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(42 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (14 : Vertex) [(42 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E257.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112257
