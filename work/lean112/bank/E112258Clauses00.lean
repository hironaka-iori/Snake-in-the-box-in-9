import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 123 = true ∨ valuation q 43 = true := by
  rw [value1, value43, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (69 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 123 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(69 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (321 : Vertex) [(69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 124 = true ∨ valuation q 4 = true := by
  rw [value2, value4, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(101 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (65 : Vertex) [(101 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 124 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(65 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (101 : Vertex) [(65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 4 = true := by
  rw [value4, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (101 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = true ∨ valuation q 5 = true := by
  rw [value2, value4, value5]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ∈ [(69 : Vertex), (103 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (101 : Vertex) [(69 : Vertex), (103 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 126 = true ∨ valuation q 5 = true := by
  rw [value4, value5, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(103 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (69 : Vertex) [(103 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 127 = true := by
  rw [value5, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (103 : Vertex) (101 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 43 = false := by
  rw [value6, value8, value15, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (261 : Vertex) (273 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 65 = false := by
  rw [value6, value8, value15, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (261 : Vertex) (273 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 43 = false ∨ valuation q 65 = false := by
  rw [value6, value8, value43, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (261 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 15 = false ∨ valuation q 43 = false ∨ valuation q 65 = false := by
  rw [value6, value15, value43, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (273 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 8 = false ∨ valuation q 43 = false := by
  rw [value8, value43, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (257 : Vertex) (261 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 43 = false ∨ valuation q 65 = false := by
  rw [value43, value65, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (257 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 25 = false ∨ valuation q 66 = false := by
  rw [value25, value66, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (258 : Vertex) (290 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 129 = true ∨ valuation q 66 = true := by
  rw [value7, value66, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (290 : Vertex) → w ∈ [(386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (290 : Vertex) [(386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 129 = true ∨ valuation q 25 = true := by
  rw [value7, value25, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(290 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (386 : Vertex) [(290 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 130 = true ∨ valuation q 9 = true ∨ valuation q 26 = true ∨ valuation q 68 = true := by
  rw [value8, value9, value26, value68, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(263 : Vertex), (293 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (257 : Vertex) [(263 : Vertex), (293 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 130 = true ∨ valuation q 6 = true ∨ valuation q 26 = true ∨ valuation q 68 = true := by
  rw [value6, value8, value26, value68, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(257 : Vertex), (293 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (263 : Vertex) [(257 : Vertex), (293 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 130 = true ∨ valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 68 = true := by
  rw [value6, value8, value9, value68, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(257 : Vertex), (263 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (293 : Vertex) [(257 : Vertex), (263 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 130 = true ∨ valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 26 = true := by
  rw [value6, value8, value9, value26, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(257 : Vertex), (263 : Vertex), (293 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (389 : Vertex) [(257 : Vertex), (263 : Vertex), (293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 9 = true := by
  rw [value9, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (263 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 18 = false := by
  rw [value8, value9, value13, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 28 = false := by
  rw [value8, value9, value13, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 69 = false := by
  rw [value8, value9, value13, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 18 = false ∨ valuation q 28 = false := by
  rw [value8, value9, value18, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (279 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 18 = false ∨ valuation q 69 = false := by
  rw [value8, value9, value18, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 28 = false ∨ valuation q 69 = false := by
  rw [value8, value9, value28, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (295 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 28 = false := by
  rw [value9, value13, value18, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 69 = false := by
  rw [value9, value13, value18, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 28 = false ∨ valuation q 69 = false := by
  rw [value9, value13, value28, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (295 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 28 = false ∨ valuation q 69 = false := by
  rw [value9, value18, value28, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (279 : Vertex) (295 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E258.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112258
