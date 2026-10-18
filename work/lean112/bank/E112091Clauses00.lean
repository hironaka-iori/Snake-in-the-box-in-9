import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 18 = false := by
  rw [value1, value2, value4, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (4 : Vertex) (8 : Vertex) (64 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 107 = true ∨ valuation q 4 = true ∨ valuation q 18 = true := by
  rw [value1, value4, value18, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(8 : Vertex), (64 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (4 : Vertex) [(8 : Vertex), (64 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 2 = true := by
  rw [value2, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (4 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (6 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (4 : Vertex) [(0 : Vertex), (6 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 108 = true ∨ valuation q 3 = true := by
  rw [value2, value3, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (0 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 108 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (6 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value2, value3, value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (4 : Vertex) (14 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 109 = true ∨ valuation q 2 = true ∨ valuation q 8 = true := by
  rw [value2, value3, value8, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(4 : Vertex), (14 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(4 : Vertex), (14 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 6 = false := by
  rw [value1, value4, value5, value6]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (10 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 13 = false := by
  rw [value1, value4, value5, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 22 = false := by
  rw [value1, value4, value5, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 67 = false := by
  rw [value1, value4, value5, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 13 = false := by
  rw [value1, value4, value6, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 22 = false := by
  rw [value1, value4, value6, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 67 = false := by
  rw [value1, value4, value6, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (10 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 22 = false := by
  rw [value1, value4, value13, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (24 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 67 = false := by
  rw [value1, value4, value13, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (24 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 22 = false ∨ valuation q 67 = false := by
  rw [value1, value4, value22, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (72 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 67 = false := by
  rw [value4, value5, value6, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (10 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 67 = false := by
  rw [value4, value5, value13, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (24 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 22 = false ∨ valuation q 67 = false := by
  rw [value4, value5, value22, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (72 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 22 = false ∨ valuation q 67 = false := by
  rw [value4, value6, value22, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (10 : Vertex) (72 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 14 = false := by
  rw [value4, value5, value7, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (8 : Vertex) (11 : Vertex) (25 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 23 = false := by
  rw [value4, value5, value7, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (8 : Vertex) (11 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value4, value5, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (8 : Vertex) (25 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value5, value7, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (11 : Vertex) (25 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value4, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (8 : Vertex) (11 : Vertex) (14 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 15 = false := by
  rw [value4, value6, value7, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (8 : Vertex) (11 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 15 = false := by
  rw [value4, value6, value8, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (8 : Vertex) (14 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 15 = false := by
  rw [value6, value7, value8, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (11 : Vertex) (14 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 7 = true := by
  rw [value7, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (11 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = true ∨ valuation q 6 = true ∨ valuation q 16 = true := by
  rw [value5, value6, value7, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ∈ [(9 : Vertex), (10 : Vertex), (27 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (11 : Vertex) [(9 : Vertex), (10 : Vertex), (27 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E091.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112091
