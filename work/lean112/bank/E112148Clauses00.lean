import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 112 = true ∨ valuation q 8 = true := by
  rw [value1, value8, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(75 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (27 : Vertex) [(75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 112 = true ∨ valuation q 3 = true := by
  rw [value1, value3, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(27 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (75 : Vertex) [(27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 113 = true := by
  rw [value2, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (25 : Vertex) (27 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 114 = true ∨ valuation q 2 = true ∨ valuation q 18 = true := by
  rw [value2, value3, value18, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(25 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (11 : Vertex) [(25 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 40 = false := by
  rw [value4, value6, value12, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (67 : Vertex) (81 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 64 = false := by
  rw [value4, value6, value12, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (67 : Vertex) (81 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 12 = false ∨ valuation q 40 = false ∨ valuation q 64 = false := by
  rw [value4, value12, value40, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (81 : Vertex) (193 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value4, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (65 : Vertex) (71 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 42 = false := by
  rw [value6, value7, value10, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (79 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 10 = false := by
  rw [value1, value6, value8, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (67 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 45 = false := by
  rw [value1, value6, value8, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (67 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 69 = false := by
  rw [value1, value6, value8, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (67 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 18 = false := by
  rw [value1, value8, value10, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (79 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 45 = false := by
  rw [value1, value8, value10, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (79 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 69 = false := by
  rw [value1, value8, value10, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (79 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value1, value8, value45, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (203 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 18 = false := by
  rw [value6, value8, value10, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (79 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 45 = false := by
  rw [value6, value8, value10, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (79 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 69 = false := by
  rw [value6, value8, value10, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (79 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 18 = false ∨ valuation q 45 = false := by
  rw [value6, value8, value18, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (91 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 18 = false ∨ valuation q 45 = false := by
  rw [value8, value10, value18, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (79 : Vertex) (91 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 18 = false ∨ valuation q 69 = false := by
  rw [value8, value10, value18, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (79 : Vertex) (91 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value8, value10, value45, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (79 : Vertex) (203 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 120 = true := by
  rw [value9, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (77 : Vertex) (79 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 21 = false := by
  rw [value7, value8, value10, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 121 = true ∨ valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 21 = true := by
  rw [value8, value9, value10, value21, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(75 : Vertex), (77 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (71 : Vertex) [(75 : Vertex), (77 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 121 = true ∨ valuation q 7 = true ∨ valuation q 8 = true ∨ valuation q 21 = true := by
  rw [value7, value8, value10, value21, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(71 : Vertex), (75 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (77 : Vertex) [(71 : Vertex), (75 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 15 = false := by
  rw [value11, value12, value13, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (81 : Vertex) (82 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 16 = false := by
  rw [value11, value12, value13, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (81 : Vertex) (82 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 16 = false := by
  rw [value11, value12, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (81 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 16 = false := by
  rw [value11, value13, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (82 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 123 = true ∨ valuation q 11 = true ∨ valuation q 14 = true := by
  rw [value11, value12, value14, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(80 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (65 : Vertex) [(80 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E148.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112148
