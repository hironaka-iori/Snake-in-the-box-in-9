import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 123 = true ∨ valuation q 6 = true := by
  rw [value1, value6, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(42 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (35 : Vertex) [(42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 123 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(35 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (42 : Vertex) [(35 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 124 = true ∨ valuation q 7 = true ∨ valuation q 17 = true := by
  rw [value2, value7, value17, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(43 : Vertex), (99 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (34 : Vertex) [(43 : Vertex), (99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 17 = true := by
  rw [value1, value2, value17, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(34 : Vertex), (99 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (43 : Vertex) [(34 : Vertex), (99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 7 = true := by
  rw [value1, value2, value7, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(34 : Vertex), (43 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (99 : Vertex) [(34 : Vertex), (43 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 10 = false := by
  rw [value3, value4, value8, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (37 : Vertex) (44 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 18 = false := by
  rw [value3, value4, value8, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (37 : Vertex) (44 : Vertex) (100 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 10 = false ∨ valuation q 18 = false := by
  rw [value3, value4, value10, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (37 : Vertex) (52 : Vertex) (100 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 18 = false := by
  rw [value3, value8, value10, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (44 : Vertex) (52 : Vertex) (100 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 125 = true ∨ valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 18 = true := by
  rw [value3, value8, value10, value18, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(44 : Vertex), (52 : Vertex), (100 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (37 : Vertex) [(44 : Vertex), (52 : Vertex), (100 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 125 = true ∨ valuation q 4 = true ∨ valuation q 8 = true ∨ valuation q 10 = true := by
  rw [value3, value4, value8, value10, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (100 : Vertex) → w ∈ [(37 : Vertex), (44 : Vertex), (52 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (100 : Vertex) [(37 : Vertex), (44 : Vertex), (52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 57 = false := by
  rw [value3, value4, value11, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (36 : Vertex) (53 : Vertex) (293 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 126 = true ∨ valuation q 11 = true ∨ valuation q 57 = true := by
  rw [value4, value11, value57, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(53 : Vertex), (293 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (36 : Vertex) [(53 : Vertex), (293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 126 = true ∨ valuation q 3 = true ∨ valuation q 57 = true := by
  rw [value3, value4, value57, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(36 : Vertex), (293 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (53 : Vertex) [(36 : Vertex), (293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 13 = false := by
  rw [value5, value6, value8, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 24 = false := by
  rw [value5, value6, value8, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 60 = false := by
  rw [value5, value6, value8, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 24 = false := by
  rw [value5, value6, value13, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (56 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 60 = false := by
  rw [value5, value6, value13, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (56 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 24 = false ∨ valuation q 60 = false := by
  rw [value5, value6, value24, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (168 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 24 = false := by
  rw [value5, value8, value13, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (44 : Vertex) (56 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 60 = false := by
  rw [value5, value8, value13, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (44 : Vertex) (56 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 24 = false ∨ valuation q 60 = false := by
  rw [value5, value8, value24, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (44 : Vertex) (168 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 60 = false := by
  rw [value5, value13, value24, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (56 : Vertex) (168 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 127 = true ∨ valuation q 6 = true ∨ valuation q 8 = true ∨ valuation q 13 = true ∨ valuation q 24 = true := by
  rw [value5, value6, value8, value13, value24, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(42 : Vertex), (44 : Vertex), (56 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (296 : Vertex) [(42 : Vertex), (44 : Vertex), (56 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 9 = false := by
  rw [value1, value5, value6, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (40 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 128 = true ∨ valuation q 5 = true ∨ valuation q 7 = true ∨ valuation q 9 = true := by
  rw [value5, value6, value7, value9, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(40 : Vertex), (43 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (34 : Vertex) [(40 : Vertex), (43 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 128 = true ∨ valuation q 1 = true ∨ valuation q 7 = true ∨ valuation q 9 = true := by
  rw [value1, value6, value7, value9, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(34 : Vertex), (43 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (40 : Vertex) [(34 : Vertex), (43 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 128 = true ∨ valuation q 1 = true ∨ valuation q 5 = true ∨ valuation q 9 = true := by
  rw [value1, value5, value6, value9, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(34 : Vertex), (40 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (43 : Vertex) [(34 : Vertex), (40 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 128 = true ∨ valuation q 1 = true ∨ valuation q 5 = true ∨ valuation q 7 = true := by
  rw [value1, value5, value6, value7, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(34 : Vertex), (40 : Vertex), (43 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (46 : Vertex) [(34 : Vertex), (40 : Vertex), (43 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 15 = false := by
  rw [value2, value6, value7, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (35 : Vertex) (42 : Vertex) (59 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 26 = false := by
  rw [value2, value6, value7, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (35 : Vertex) (42 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.First112
