import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 10 = false := by
  rw [value1, value2, value3, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (1 : Vertex) (2 : Vertex) (16 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 111 = true ∨ valuation q 3 = true ∨ valuation q 10 = true := by
  rw [value1, value3, value10, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(2 : Vertex), (16 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(2 : Vertex), (16 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 11 = true := by
  rw [value1, value2, value4, value5, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (3 : Vertex), (5 : Vertex), (17 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (1 : Vertex) [(0 : Vertex), (3 : Vertex), (5 : Vertex), (17 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 112 = true ∨ valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 11 = true := by
  rw [value2, value4, value5, value11, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(3 : Vertex), (5 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(3 : Vertex), (5 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 112 = true ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value1, value2, value4, value11, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(0 : Vertex), (3 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (5 : Vertex) [(0 : Vertex), (3 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 112 = true ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 5 = true := by
  rw [value1, value2, value4, value5, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex), (3 : Vertex), (5 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex), (3 : Vertex), (5 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 20 = false := by
  rw [value3, value4, value6, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (3 : Vertex) (6 : Vertex) (66 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 67 = false := by
  rw [value3, value12, value20, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (18 : Vertex) (66 : Vertex) (258 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 7 = false := by
  rw [value2, value3, value4, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (1 : Vertex) (2 : Vertex) (11 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 13 = false := by
  rw [value2, value3, value4, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (1 : Vertex) (2 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 21 = false := by
  rw [value2, value4, value7, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (1 : Vertex) (11 : Vertex) (67 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value2, value4, value13, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (1 : Vertex) (19 : Vertex) (67 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 13 = false := by
  rw [value3, value4, value7, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (2 : Vertex) (11 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 21 = false := by
  rw [value3, value4, value7, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (2 : Vertex) (11 : Vertex) (67 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value4, value7, value13, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (11 : Vertex) (19 : Vertex) (67 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 23 = false := by
  rw [value2, value5, value8, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (13 : Vertex) (69 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 68 = false := by
  rw [value2, value5, value8, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (13 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 2 = false ∨ valuation q 23 = false ∨ valuation q 68 = false := by
  rw [value2, value5, value23, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (69 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 68 = false := by
  rw [value5, value8, value23, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (13 : Vertex) (69 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 115 = true ∨ valuation q 2 = true ∨ valuation q 8 = true ∨ valuation q 23 = true := by
  rw [value2, value5, value8, value23, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(1 : Vertex), (13 : Vertex), (69 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (261 : Vertex) [(1 : Vertex), (13 : Vertex), (69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 69 = false := by
  rw [value3, value6, value14, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (2 : Vertex) (22 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 25 = true ∨ valuation q 70 = true := by
  rw [value4, value7, value9, value25, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ∈ [(3 : Vertex), (15 : Vertex), (75 : Vertex), (267 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (11 : Vertex) [(3 : Vertex), (15 : Vertex), (75 : Vertex), (267 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 117 = true ∨ valuation q 9 = true ∨ valuation q 25 = true ∨ valuation q 70 = true := by
  rw [value7, value9, value25, value70, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(15 : Vertex), (75 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (3 : Vertex) [(15 : Vertex), (75 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 117 = true ∨ valuation q 4 = true ∨ valuation q 25 = true ∨ valuation q 70 = true := by
  rw [value4, value7, value25, value70, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(3 : Vertex), (75 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (15 : Vertex) [(3 : Vertex), (75 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 117 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 25 = true := by
  rw [value4, value7, value9, value25, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(3 : Vertex), (15 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (267 : Vertex) [(3 : Vertex), (15 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 17 = false := by
  rw [value5, value8, value9, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (5 : Vertex) (15 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 118 = true ∨ valuation q 5 = true ∨ valuation q 9 = true := by
  rw [value5, value8, value9, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(5 : Vertex), (15 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (29 : Vertex) [(5 : Vertex), (15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 19 = false := by
  rw [value7, value8, value9, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (11 : Vertex) (13 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 119 = true ∨ valuation q 8 = true ∨ valuation q 19 = true := by
  rw [value8, value9, value19, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(13 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (11 : Vertex) [(13 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 119 = true ∨ valuation q 7 = true ∨ valuation q 19 = true := by
  rw [value7, value9, value19, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(11 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (13 : Vertex) [(11 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 2 = false ∨ valuation q 10 = false ∨ valuation q 13 = false := by
  rw [value2, value10, value11, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (16 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 13 = false := by
  rw [value3, value10, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (16 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E183.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112183
