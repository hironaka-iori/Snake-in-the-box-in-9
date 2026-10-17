import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 22 = false := by
  rw [value1, value4, value7, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (38 : Vertex) (42 : Vertex) (98 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 77 = false := by
  rw [value1, value4, value7, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (38 : Vertex) (42 : Vertex) (290 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 22 = false ∨ valuation q 77 = false := by
  rw [value1, value7, value22, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (42 : Vertex) (98 : Vertex) (290 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 9 = false := by
  rw [value2, value3, value4, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (37 : Vertex) (38 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 122 = true ∨ valuation q 4 = true ∨ valuation q 9 = true := by
  rw [value2, value4, value9, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(38 : Vertex), (44 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (37 : Vertex) [(38 : Vertex), (44 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 123 = true ∨ valuation q 14 = true := by
  rw [value3, value14, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(53 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (36 : Vertex) [(53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 123 = true ∨ valuation q 2 = true := by
  rw [value2, value3, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(36 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (53 : Vertex) [(36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 10 = false := by
  rw [value1, value2, value4, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (36 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 124 = true ∨ valuation q 2 = true ∨ valuation q 10 = true := by
  rw [value2, value4, value10, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(36 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (34 : Vertex) [(36 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 10 = true := by
  rw [value1, value4, value10, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(34 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (36 : Vertex) [(34 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value4, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(34 : Vertex), (36 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (46 : Vertex) [(34 : Vertex), (36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 9 = false := by
  rw [value5, value6, value7, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 16 = false := by
  rw [value5, value6, value7, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 47 = false := by
  rw [value5, value6, value7, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 80 = false := by
  rw [value5, value6, value7, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 16 = false := by
  rw [value5, value6, value9, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (44 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 47 = false := by
  rw [value5, value6, value9, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (44 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 80 = false := by
  rw [value5, value6, value9, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (44 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 16 = false ∨ valuation q 47 = false := by
  rw [value5, value6, value16, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (56 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 16 = false ∨ valuation q 80 = false := by
  rw [value5, value6, value16, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (56 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 47 = false ∨ valuation q 80 = false := by
  rw [value5, value6, value47, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (168 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 16 = false := by
  rw [value5, value7, value9, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 47 = false := by
  rw [value5, value7, value9, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 80 = false := by
  rw [value5, value7, value9, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 16 = false ∨ valuation q 47 = false := by
  rw [value5, value7, value16, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (56 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 16 = false ∨ valuation q 80 = false := by
  rw [value5, value7, value16, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (56 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 47 = false ∨ valuation q 80 = false := by
  rw [value5, value7, value47, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (168 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 47 = false := by
  rw [value5, value9, value16, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (44 : Vertex) (56 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 80 = false := by
  rw [value5, value9, value16, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (44 : Vertex) (56 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 47 = false ∨ valuation q 80 = false := by
  rw [value5, value9, value47, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (44 : Vertex) (168 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 16 = false ∨ valuation q 47 = false ∨ valuation q 80 = false := by
  rw [value5, value16, value47, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (56 : Vertex) (168 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 125 = true ∨ valuation q 7 = true ∨ valuation q 9 = true ∨ valuation q 16 = true ∨ valuation q 47 = true ∨ valuation q 80 = true := by
  rw [value5, value7, value9, value16, value47, value80, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(42 : Vertex), (44 : Vertex), (56 : Vertex), (168 : Vertex), (296 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (41 : Vertex) [(42 : Vertex), (44 : Vertex), (56 : Vertex), (168 : Vertex), (296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E040.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112040
