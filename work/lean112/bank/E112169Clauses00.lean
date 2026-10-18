import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true := by
  rw [value1, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (5 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (1 : Vertex) [(0 : Vertex), (5 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (5 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 52 = false := by
  rw [value2, value3, value5, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (13 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 2 = true ∨ valuation q 52 = true := by
  rw [value2, value3, value52, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(1 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (13 : Vertex) [(1 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 2 = true ∨ valuation q 5 = true := by
  rw [value2, value3, value5, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(1 : Vertex), (13 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (261 : Vertex) [(1 : Vertex), (13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 120 = true ∨ valuation q 53 = true := by
  rw [value4, value53, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(267 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (15 : Vertex) [(267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 120 = true ∨ valuation q 6 = true := by
  rw [value4, value6, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(15 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (267 : Vertex) [(15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 3 = false ∨ valuation q 6 = false := by
  rw [value3, value6, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (13 : Vertex) (5 : Vertex) (15 : Vertex) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 6 = true := by
  rw [value5, value6, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(15 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (5 : Vertex) [(15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 3 = true := by
  rw [value3, value5, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(5 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (15 : Vertex) [(5 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 5 = true := by
  rw [value5, value6, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(13 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (11 : Vertex) [(13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 4 = true := by
  rw [value4, value6, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(11 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (13 : Vertex) [(11 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 31 = false := by
  rw [value7, value8, value9, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (97 : Vertex) (104 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 9 = true ∨ valuation q 31 = true := by
  rw [value7, value9, value31, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (97 : Vertex) → w ∈ [(104 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (97 : Vertex) [(104 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 8 = true ∨ valuation q 31 = true := by
  rw [value7, value8, value31, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(97 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (104 : Vertex) [(97 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 8 = true := by
  rw [value8, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (97 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 7 = false ∨ valuation q 10 = false ∨ valuation q 32 = false := by
  rw [value7, value8, value10, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (97 : Vertex) (96 : Vertex) (113 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 10 = false ∨ valuation q 32 = false := by
  rw [value10, value32, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (97 : Vertex) (113 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 7 = true ∨ valuation q 32 = true := by
  rw [value7, value8, value32, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(96 : Vertex), (225 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (113 : Vertex) [(96 : Vertex), (225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 9 = true := by
  rw [value9, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (104 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = true ∨ valuation q 37 = true := by
  rw [value7, value9, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ∈ [(96 : Vertex), (232 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (104 : Vertex) [(96 : Vertex), (232 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 37 = true := by
  rw [value9, value37, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(232 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (96 : Vertex) [(232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 7 = true := by
  rw [value7, value9, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(96 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (232 : Vertex) [(96 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = true ∨ valuation q 42 = true := by
  rw [value8, value10, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ∈ [(97 : Vertex), (241 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (113 : Vertex) [(97 : Vertex), (241 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 8 = false ∨ valuation q 42 = false := by
  rw [value8, value42, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (113 : Vertex) (97 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 10 = true := by
  rw [value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 126 = true := by
  rw [value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 17 = false := by
  rw [value11, value12, value13, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value11, value12, value13, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 31 = false := by
  rw [value11, value12, value13, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value11, value12, value17, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E169.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112169
