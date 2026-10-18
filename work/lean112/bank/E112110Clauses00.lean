import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = true ∨ valuation q 6 = true ∨ valuation q 22 = true ∨ valuation q 52 = true := by
  rw [value1, value2, value6, value22, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ∈ [(14 : Vertex), (74 : Vertex), (138 : Vertex), (266 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (10 : Vertex) [(14 : Vertex), (74 : Vertex), (138 : Vertex), (266 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 22 = false ∨ valuation q 52 = false := by
  rw [value1, value6, value22, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (74 : Vertex) (138 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 6 = false ∨ valuation q 22 = false := by
  rw [value6, value22, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (10 : Vertex) (74 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 22 = false ∨ valuation q 52 = false := by
  rw [value22, value52, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (10 : Vertex) (138 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 119 = true ∨ valuation q 2 = true ∨ valuation q 22 = true ∨ valuation q 52 = true := by
  rw [value1, value2, value22, value52, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(14 : Vertex), (138 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (74 : Vertex) [(14 : Vertex), (138 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 119 = true ∨ valuation q 2 = true ∨ valuation q 6 = true ∨ valuation q 52 = true := by
  rw [value1, value2, value6, value52, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(14 : Vertex), (74 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (138 : Vertex) [(14 : Vertex), (74 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 119 = true ∨ valuation q 2 = true ∨ valuation q 6 = true ∨ valuation q 22 = true := by
  rw [value1, value2, value6, value22, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(14 : Vertex), (74 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (266 : Vertex) [(14 : Vertex), (74 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 120 = true := by
  rw [value2, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (14 : Vertex) (10 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 6 = true := by
  rw [value3, value6, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(74 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (67 : Vertex) [(74 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 4 = true := by
  rw [value3, value4, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(67 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (74 : Vertex) [(67 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 122 = true ∨ valuation q 7 = true ∨ valuation q 12 = true := by
  rw [value4, value7, value12, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(75 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (66 : Vertex) [(75 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 122 = true ∨ valuation q 3 = true ∨ valuation q 7 = true := by
  rw [value3, value4, value7, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(66 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (83 : Vertex) [(66 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true := by
  rw [value5, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (69 : Vertex) (77 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 3 = true ∨ valuation q 7 = true := by
  rw [value3, value6, value7, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(66 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (10 : Vertex) [(66 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 7 = true := by
  rw [value1, value6, value7, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(10 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (66 : Vertex) [(10 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 3 = true := by
  rw [value1, value3, value6, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(10 : Vertex), (66 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (75 : Vertex) [(10 : Vertex), (66 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 9 = false := by
  rw [value4, value6, value7, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (74 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 40 = false := by
  rw [value4, value6, value7, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (74 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 64 = false := by
  rw [value4, value6, value7, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (74 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 40 = false := by
  rw [value4, value7, value9, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (79 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 64 = false := by
  rw [value4, value7, value9, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (79 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 40 = false ∨ valuation q 64 = false := by
  rw [value4, value7, value40, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (203 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 40 = false := by
  rw [value6, value7, value9, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (74 : Vertex) (79 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 64 = false := by
  rw [value6, value7, value9, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (74 : Vertex) (79 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 40 = false ∨ valuation q 64 = false := by
  rw [value6, value7, value40, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (74 : Vertex) (203 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 40 = false ∨ valuation q 64 = false := by
  rw [value7, value9, value40, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (79 : Vertex) (203 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 5 = true ∨ valuation q 9 = true := by
  rw [value5, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ∈ [(69 : Vertex), (79 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (77 : Vertex) [(69 : Vertex), (79 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 126 = true ∨ valuation q 5 = true := by
  rw [value5, value8, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(69 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (79 : Vertex) [(69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 7 = true ∨ valuation q 17 = true := by
  rw [value7, value9, value17, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(75 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (77 : Vertex) [(75 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 7 = true ∨ valuation q 8 = true := by
  rw [value7, value8, value9, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(75 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (95 : Vertex) [(75 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value10, value11, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (81 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 128 = true ∨ valuation q 13 = true ∨ valuation q 14 = true := by
  rw [value10, value13, value14, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(84 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (81 : Vertex) [(84 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E110.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112110
