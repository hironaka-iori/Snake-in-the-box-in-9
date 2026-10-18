import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 121 = true ∨ valuation q 3 = true := by
  rw [value1, value3, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(38 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (37 : Vertex) [(38 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 121 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(37 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (38 : Vertex) [(37 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 122 = true ∨ valuation q 11 = true := by
  rw [value2, value11, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(53 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (36 : Vertex) [(53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 122 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(36 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (53 : Vertex) [(36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 123 = true ∨ valuation q 8 = true := by
  rw [value3, value8, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(46 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (36 : Vertex) [(46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 123 = true ∨ valuation q 1 = true := by
  rw [value1, value3, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(36 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (46 : Vertex) [(36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 13 = false := by
  rw [value4, value5, value6, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 21 = false := by
  rw [value4, value5, value6, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value4, value5, value13, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (56 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value4, value6, value13, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (42 : Vertex) (56 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value13, value21, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (40 : Vertex) (56 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 39 = false := by
  rw [value5, value7, value14, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (43 : Vertex) (57 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 125 = true ∨ valuation q 7 = true ∨ valuation q 14 = true ∨ valuation q 39 = true := by
  rw [value5, value7, value14, value39, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(43 : Vertex), (57 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (40 : Vertex) [(43 : Vertex), (57 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 125 = true ∨ valuation q 4 = true ∨ valuation q 14 = true ∨ valuation q 39 = true := by
  rw [value4, value5, value14, value39, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(40 : Vertex), (57 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (43 : Vertex) [(40 : Vertex), (57 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 125 = true ∨ valuation q 4 = true ∨ valuation q 7 = true ∨ valuation q 39 = true := by
  rw [value4, value5, value7, value39, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(40 : Vertex), (43 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (57 : Vertex) [(40 : Vertex), (43 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 125 = true ∨ valuation q 4 = true ∨ valuation q 7 = true ∨ valuation q 14 = true := by
  rw [value4, value5, value7, value14, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(40 : Vertex), (43 : Vertex), (57 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (169 : Vertex) [(40 : Vertex), (43 : Vertex), (57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value4, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (40 : Vertex) (43 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 7 = true ∨ valuation q 8 = true := by
  rw [value6, value7, value8, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(43 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (40 : Vertex) [(43 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 4 = true ∨ valuation q 8 = true := by
  rw [value4, value6, value8, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(40 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (43 : Vertex) [(40 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 4 = true ∨ valuation q 7 = true := by
  rw [value4, value6, value7, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(40 : Vertex), (43 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (46 : Vertex) [(40 : Vertex), (43 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 40 = false := by
  rw [value5, value6, value7, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (41 : Vertex) (42 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 5 = false ∨ valuation q 6 = false := by
  rw [value5, value6, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (43 : Vertex) (41 : Vertex) (42 : Vertex) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 5 = false ∨ valuation q 40 = false := by
  rw [value5, value40, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (43 : Vertex) (41 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 127 = true ∨ valuation q 6 = true ∨ valuation q 40 = true := by
  rw [value6, value7, value40, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (43 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(42 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (43 : Vertex) (41 : Vertex) [(42 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 127 = true ∨ valuation q 5 = true ∨ valuation q 40 = true := by
  rw [value5, value7, value40, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (43 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(41 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (43 : Vertex) (42 : Vertex) [(41 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 15 = false := by
  rw [value3, value6, value8, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (46 : Vertex) (38 : Vertex) (42 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 128 = true ∨ valuation q 6 = true ∨ valuation q 15 = true := by
  rw [value6, value8, value15, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(42 : Vertex), (62 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (38 : Vertex) [(42 : Vertex), (62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 128 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value3, value6, value8, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(38 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (62 : Vertex) [(38 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = true ∨ valuation q 24 = true ∨ valuation q 44 = true := by
  rw [value9, value13, value24, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ∈ [(56 : Vertex), (112 : Vertex), (176 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (48 : Vertex) [(56 : Vertex), (112 : Vertex), (176 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 44 = false := by
  rw [value9, value13, value24, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (48 : Vertex) (56 : Vertex) (112 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 13 = false ∨ valuation q 44 = false := by
  rw [value13, value44, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (48 : Vertex) (56 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 129 = true ∨ valuation q 24 = true ∨ valuation q 44 = true := by
  rw [value9, value24, value44, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (56 : Vertex) → w ∈ [(112 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (56 : Vertex) [(112 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E004.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112004
