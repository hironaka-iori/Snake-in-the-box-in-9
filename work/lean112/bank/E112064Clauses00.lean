import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 1 = true := by
  rw [value1, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (68 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ∈ [(69 : Vertex), (70 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (68 : Vertex) [(69 : Vertex), (70 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 2 = false ∨ valuation q 3 = false := by
  rw [value2, value3, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (68 : Vertex) (69 : Vertex) (70 : Vertex) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 3 = true := by
  rw [value1, value3, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(70 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (69 : Vertex) [(70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(69 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (70 : Vertex) [(69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 32 = false := by
  rw [value1, value2, value11, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (85 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 119 = true ∨ valuation q 11 = true ∨ valuation q 32 = true := by
  rw [value2, value11, value32, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(85 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (68 : Vertex) [(85 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 32 = true := by
  rw [value1, value2, value32, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(68 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (85 : Vertex) [(68 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 119 = true ∨ valuation q 1 = true ∨ valuation q 11 = true := by
  rw [value1, value2, value11, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(68 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (197 : Vertex) [(68 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 120 = true ∨ valuation q 8 = true := by
  rw [value3, value8, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(78 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (68 : Vertex) [(78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 120 = true ∨ valuation q 1 = true := by
  rw [value1, value3, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(68 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (78 : Vertex) [(68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 13 = false := by
  rw [value4, value5, value6, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (73 : Vertex) (74 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 5 = false ∨ valuation q 6 = false := by
  rw [value5, value6, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (72 : Vertex) (73 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 5 = false ∨ valuation q 13 = false := by
  rw [value5, value13, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (72 : Vertex) (73 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 6 = true ∨ valuation q 13 = true := by
  rw [value4, value6, value13, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(74 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (73 : Vertex) [(74 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 14 = false := by
  rw [value4, value5, value7, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (75 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 69 = false := by
  rw [value4, value5, value7, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (75 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 69 = false := by
  rw [value4, value5, value14, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (89 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 69 = false := by
  rw [value5, value7, value14, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (75 : Vertex) (89 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 7 = true ∨ valuation q 14 = true ∨ valuation q 69 = true := by
  rw [value5, value7, value14, value69, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(75 : Vertex), (89 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (72 : Vertex) [(75 : Vertex), (89 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 4 = true ∨ valuation q 14 = true ∨ valuation q 69 = true := by
  rw [value4, value5, value14, value69, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(72 : Vertex), (89 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (75 : Vertex) [(72 : Vertex), (89 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 4 = true ∨ valuation q 7 = true ∨ valuation q 69 = true := by
  rw [value4, value5, value7, value69, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(72 : Vertex), (75 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (89 : Vertex) [(72 : Vertex), (75 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value4, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (74 : Vertex) (72 : Vertex) (75 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 123 = true ∨ valuation q 4 = true ∨ valuation q 8 = true := by
  rw [value4, value6, value8, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(72 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (75 : Vertex) [(72 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 123 = true ∨ valuation q 4 = true ∨ valuation q 7 = true := by
  rw [value4, value6, value7, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(72 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (78 : Vertex) [(72 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 70 = false := by
  rw [value5, value6, value7, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (73 : Vertex) (74 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 5 = false ∨ valuation q 6 = false := by
  rw [value5, value6, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (75 : Vertex) (73 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 70 = true := by
  rw [value6, value7, value70, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(74 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (73 : Vertex) [(74 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 124 = true ∨ valuation q 5 = true ∨ valuation q 70 = true := by
  rw [value5, value7, value70, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(73 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (74 : Vertex) [(73 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 16 = false := by
  rw [value3, value6, value8, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (70 : Vertex) (74 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 3 = false ∨ valuation q 6 = false := by
  rw [value3, value6, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (78 : Vertex) (70 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 125 = true ∨ valuation q 6 = true ∨ valuation q 16 = true := by
  rw [value6, value8, value16, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(74 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (70 : Vertex) [(74 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E064.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112064
