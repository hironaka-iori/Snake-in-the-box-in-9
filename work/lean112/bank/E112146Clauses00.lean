import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 13 = false := by
  rw [value1, value2, value6, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (11 : Vertex) (26 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 115 = true ∨ valuation q 2 = true ∨ valuation q 13 = true := by
  rw [value1, value2, value13, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (26 : Vertex) → w ∈ [(11 : Vertex), (74 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (26 : Vertex) [(11 : Vertex), (74 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 116 = true ∨ valuation q 14 = true ∨ valuation q 34 = true := by
  rw [value2, value14, value34, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (10 : Vertex) [(75 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 116 = true ∨ valuation q 1 = true ∨ valuation q 34 = true := by
  rw [value1, value2, value34, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(10 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (75 : Vertex) [(10 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 116 = true ∨ valuation q 1 = true ∨ valuation q 14 = true := by
  rw [value1, value2, value14, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(10 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (139 : Vertex) [(10 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 16 = false ∨ valuation q 36 = false := by
  rw [value3, value7, value16, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (29 : Vertex) (77 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 117 = true ∨ valuation q 16 = true ∨ valuation q 36 = true := by
  rw [value3, value16, value36, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(77 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (29 : Vertex) [(77 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 23 = false := by
  rw [value4, value5, value6, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (24 : Vertex) (25 : Vertex) (26 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 118 = true ∨ valuation q 6 = true ∨ valuation q 23 = true := by
  rw [value4, value6, value23, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(26 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (25 : Vertex) [(26 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 119 = true ∨ valuation q 7 = true := by
  rw [value5, value7, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (24 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 119 = true ∨ valuation q 4 = true := by
  rw [value4, value5, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(24 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (29 : Vertex) [(24 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 120 = true ∨ valuation q 4 = true ∨ valuation q 24 = true := by
  rw [value4, value6, value24, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(24 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (26 : Vertex) (10 : Vertex) [(24 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 120 = true ∨ valuation q 1 = true ∨ valuation q 24 = true := by
  rw [value1, value6, value24, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(10 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (26 : Vertex) (24 : Vertex) [(10 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 3 = false ∨ valuation q 5 = false := by
  rw [value3, value5, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (29 : Vertex) (13 : Vertex) (25 : Vertex) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 121 = true ∨ valuation q 3 = true := by
  rw [value3, value7, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(13 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (25 : Vertex) [(13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 12 = false := by
  rw [value8, value9, value10, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (67 : Vertex) (69 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 20 = false := by
  rw [value8, value10, value12, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (69 : Vertex) (73 : Vertex) (81 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 124 = true ∨ valuation q 11 = true ∨ valuation q 16 = true := by
  rw [value10, value11, value16, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(71 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (65 : Vertex) [(71 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 124 = true ∨ valuation q 8 = true ∨ valuation q 16 = true := by
  rw [value8, value10, value16, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(65 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (71 : Vertex) [(65 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 124 = true ∨ valuation q 8 = true ∨ valuation q 11 = true := by
  rw [value8, value10, value11, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(65 : Vertex), (71 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (77 : Vertex) [(65 : Vertex), (71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 125 = true ∨ valuation q 9 = true ∨ valuation q 18 = true := by
  rw [value9, value11, value18, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(67 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (69 : Vertex) [(67 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 126 = true ∨ valuation q 14 = true ∨ valuation q 16 = true := by
  rw [value12, value14, value16, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(75 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (65 : Vertex) [(75 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 126 = true ∨ valuation q 8 = true ∨ valuation q 16 = true := by
  rw [value8, value12, value16, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(65 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (75 : Vertex) [(65 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 126 = true ∨ valuation q 8 = true ∨ valuation q 14 = true := by
  rw [value8, value12, value14, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(65 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (77 : Vertex) [(65 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 1 = false ∨ valuation q 50 = false ∨ valuation q 71 = false := by
  rw [value1, value13, value50, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (74 : Vertex) (10 : Vertex) (202 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 9 = false ∨ valuation q 13 = false := by
  rw [value2, value9, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (67 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 9 = false ∨ valuation q 51 = false := by
  rw [value2, value9, value14, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (67 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 9 = false ∨ valuation q 72 = false := by
  rw [value2, value9, value14, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (67 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value2, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (73 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 18 = false := by
  rw [value2, value12, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (73 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 51 = false := by
  rw [value2, value12, value14, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (73 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 18 = false := by
  rw [value2, value13, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (74 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E146.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112146
