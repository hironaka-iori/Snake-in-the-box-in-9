import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 33 = true := by
  rw [value1, value3, value5, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ∈ [(103 : Vertex), (107 : Vertex), (227 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (99 : Vertex) [(103 : Vertex), (107 : Vertex), (227 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 33 = false := by
  rw [value1, value3, value5, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (103 : Vertex) (107 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 5 = true ∨ valuation q 33 = true := by
  rw [value1, value5, value33, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(107 : Vertex), (227 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (103 : Vertex) [(107 : Vertex), (227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 3 = true ∨ valuation q 33 = true := by
  rw [value1, value3, value33, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(103 : Vertex), (227 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (107 : Vertex) [(103 : Vertex), (227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 3 = true ∨ valuation q 5 = true := by
  rw [value1, value3, value5, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(103 : Vertex), (107 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (227 : Vertex) [(103 : Vertex), (107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 35 = true := by
  rw [value2, value3, value6, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ∈ [(103 : Vertex), (109 : Vertex), (229 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (101 : Vertex) [(103 : Vertex), (109 : Vertex), (229 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 35 = false := by
  rw [value2, value3, value6, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (101 : Vertex) (103 : Vertex) (109 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 3 = false ∨ valuation q 6 = false := by
  rw [value3, value6, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (101 : Vertex) (103 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 3 = true ∨ valuation q 35 = true := by
  rw [value2, value3, value35, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(103 : Vertex), (229 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (109 : Vertex) [(103 : Vertex), (229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value2, value3, value6, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(103 : Vertex), (109 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (229 : Vertex) [(103 : Vertex), (109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 7 = false := by
  rw [value1, value2, value3, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (103 : Vertex) (99 : Vertex) (101 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 37 = false := by
  rw [value1, value2, value3, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (103 : Vertex) (99 : Vertex) (101 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 37 = false := by
  rw [value1, value3, value7, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (103 : Vertex) (99 : Vertex) (111 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 2 = true ∨ valuation q 7 = true ∨ valuation q 37 = true := by
  rw [value2, value3, value7, value37, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(101 : Vertex), (111 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (99 : Vertex) [(101 : Vertex), (111 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 7 = true ∨ valuation q 37 = true := by
  rw [value1, value3, value7, value37, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(99 : Vertex), (111 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (101 : Vertex) [(99 : Vertex), (111 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 2 = true ∨ valuation q 37 = true := by
  rw [value1, value2, value3, value37, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(99 : Vertex), (101 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (111 : Vertex) [(99 : Vertex), (101 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 2 = true ∨ valuation q 7 = true := by
  rw [value1, value2, value3, value7, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(99 : Vertex), (101 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (231 : Vertex) [(99 : Vertex), (101 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = true ∨ valuation q 40 = true := by
  rw [value4, value5, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ∈ [(107 : Vertex), (234 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (106 : Vertex) [(107 : Vertex), (234 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 5 = false ∨ valuation q 40 = false := by
  rw [value5, value40, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (106 : Vertex) (107 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 120 = true ∨ valuation q 40 = true := by
  rw [value4, value40, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(234 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (107 : Vertex) [(234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 120 = true ∨ valuation q 5 = true := by
  rw [value4, value5, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(107 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (234 : Vertex) [(107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 41 = false := by
  rw [value1, value4, value5, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (99 : Vertex) (106 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 41 = false := by
  rw [value1, value5, value7, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (99 : Vertex) (111 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 4 = true ∨ valuation q 7 = true ∨ valuation q 41 = true := by
  rw [value4, value5, value7, value41, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(106 : Vertex), (111 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (99 : Vertex) [(106 : Vertex), (111 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 7 = true ∨ valuation q 41 = true := by
  rw [value1, value5, value7, value41, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(99 : Vertex), (111 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (106 : Vertex) [(99 : Vertex), (111 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 41 = true := by
  rw [value1, value4, value5, value41, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(99 : Vertex), (106 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (111 : Vertex) [(99 : Vertex), (106 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 7 = true := by
  rw [value1, value4, value5, value7, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(99 : Vertex), (106 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (235 : Vertex) [(99 : Vertex), (106 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 10 = false := by
  rw [value2, value6, value7, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (109 : Vertex) (101 : Vertex) (111 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 2 = true ∨ valuation q 7 = true := by
  rw [value2, value6, value7, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(101 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (125 : Vertex) [(101 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 6 = false := by
  rw [value3, value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (103 : Vertex) (107 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 73 = false := by
  rw [value3, value6, value7, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (103 : Vertex) (109 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 73 = false := by
  rw [value5, value6, value7, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (107 : Vertex) (109 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E088.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112088
