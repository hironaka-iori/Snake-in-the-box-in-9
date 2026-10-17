import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 119 = true ∨ valuation q 14 = true := by
  rw [value1, value14, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (8 : Vertex) [(128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 120 = true ∨ valuation q 7 = true := by
  rw [value2, value7, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (14 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 120 = true ∨ valuation q 5 = true := by
  rw [value2, value5, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(14 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(14 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 10 = true := by
  rw [value1, value3, value10, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(0 : Vertex), (72 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (12 : Vertex) [(0 : Vertex), (72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 4 = true := by
  rw [value1, value3, value4, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(0 : Vertex), (12 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (72 : Vertex) [(0 : Vertex), (12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 122 = true ∨ valuation q 5 = true := by
  rw [value4, value5, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(14 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (8 : Vertex) [(14 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 122 = true ∨ valuation q 3 = true := by
  rw [value3, value4, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(8 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (14 : Vertex) [(8 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 4 = true := by
  rw [value4, value5, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(12 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (6 : Vertex) [(12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 2 = true := by
  rw [value2, value5, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (12 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 12 = false ∨ valuation q 26 = false := by
  rw [value6, value7, value12, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (22 : Vertex) (82 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 12 = false ∨ valuation q 55 = false := by
  rw [value6, value7, value12, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (22 : Vertex) (82 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 55 = false := by
  rw [value6, value7, value26, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (22 : Vertex) (146 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 12 = true ∨ valuation q 26 = true ∨ valuation q 55 = true := by
  rw [value6, value12, value26, value55, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(82 : Vertex), (146 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(82 : Vertex), (146 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 125 = true ∨ valuation q 6 = true ∨ valuation q 58 = true := by
  rw [value6, value7, value58, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(18 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(18 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 125 = true ∨ valuation q 2 = true ∨ valuation q 58 = true := by
  rw [value2, value7, value58, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(6 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(6 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 125 = true ∨ valuation q 2 = true ∨ valuation q 6 = true := by
  rw [value2, value6, value7, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(6 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (278 : Vertex) [(6 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 34 = false ∨ valuation q 64 = false := by
  rw [value8, value11, value34, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (81 : Vertex) (193 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 126 = true ∨ valuation q 11 = true ∨ valuation q 34 = true := by
  rw [value8, value11, value34, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(81 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (321 : Vertex) [(81 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 65 = true := by
  rw [value9, value65, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(322 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (82 : Vertex) [(322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 37 = false ∨ valuation q 68 = false := by
  rw [value3, value10, value37, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (8 : Vertex) (200 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 128 = true ∨ valuation q 37 = true ∨ valuation q 68 = true := by
  rw [value10, value37, value68, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(200 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (8 : Vertex) [(200 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 11 = true := by
  rw [value11, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (81 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = true ∨ valuation q 13 = true := by
  rw [value8, value11, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ∈ [(65 : Vertex), (83 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (81 : Vertex) [(65 : Vertex), (83 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 129 = true ∨ valuation q 13 = true := by
  rw [value11, value13, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(83 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (65 : Vertex) [(83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 129 = true ∨ valuation q 8 = true := by
  rw [value8, value11, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(65 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (83 : Vertex) [(65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 41 = false := by
  rw [value6, value12, value13, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (83 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 73 = false := by
  rw [value6, value12, value13, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (83 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 6 = false ∨ valuation q 41 = false ∨ valuation q 73 = false := by
  rw [value6, value12, value41, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (210 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 41 = false ∨ valuation q 73 = false := by
  rw [value12, value13, value41, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (83 : Vertex) (210 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 41 = true ∨ valuation q 73 = true := by
  rw [value6, value9, value12, value41, value73, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(18 : Vertex), (66 : Vertex), (210 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (83 : Vertex) [(18 : Vertex), (66 : Vertex), (210 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 13 = true ∨ valuation q 41 = true := by
  rw [value6, value9, value12, value13, value41, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(18 : Vertex), (66 : Vertex), (83 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (338 : Vertex) [(18 : Vertex), (66 : Vertex), (83 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 12 = true := by
  rw [value12, value13, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(82 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (81 : Vertex) [(82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E007.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112007
