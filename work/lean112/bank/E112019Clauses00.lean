import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 122 = true := by
  rw [value1, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (4 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 25 = false := by
  rw [value2, value4, value8, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (4 : Vertex) (12 : Vertex) (68 : Vertex) (132 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 123 = true ∨ valuation q 1 = true ∨ valuation q 8 = true ∨ valuation q 25 = true := by
  rw [value1, value2, value8, value25, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(0 : Vertex), (68 : Vertex), (132 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (12 : Vertex) [(0 : Vertex), (68 : Vertex), (132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 123 = true ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 25 = true := by
  rw [value1, value2, value4, value25, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(0 : Vertex), (12 : Vertex), (132 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (68 : Vertex) [(0 : Vertex), (12 : Vertex), (132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 123 = true ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 8 = true := by
  rw [value1, value2, value4, value8, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(0 : Vertex), (12 : Vertex), (68 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (132 : Vertex) [(0 : Vertex), (12 : Vertex), (68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 11 = false ∨ valuation q 28 = false := by
  rw [value3, value5, value11, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (14 : Vertex) (74 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 11 = false ∨ valuation q 58 = false := by
  rw [value3, value5, value11, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (14 : Vertex) (74 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 28 = false ∨ valuation q 58 = false := by
  rw [value3, value5, value28, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (14 : Vertex) (138 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 28 = false ∨ valuation q 58 = false := by
  rw [value3, value11, value28, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (74 : Vertex) (138 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 124 = true ∨ valuation q 11 = true ∨ valuation q 28 = true ∨ valuation q 58 = true := by
  rw [value3, value11, value28, value58, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(74 : Vertex), (138 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (14 : Vertex) [(74 : Vertex), (138 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 124 = true ∨ valuation q 5 = true ∨ valuation q 28 = true ∨ valuation q 58 = true := by
  rw [value3, value5, value28, value58, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(14 : Vertex), (138 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (74 : Vertex) [(14 : Vertex), (138 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 124 = true ∨ valuation q 5 = true ∨ valuation q 11 = true ∨ valuation q 58 = true := by
  rw [value3, value5, value11, value58, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(14 : Vertex), (74 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (138 : Vertex) [(14 : Vertex), (74 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 125 = true ∨ valuation q 5 = true := by
  rw [value4, value5, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(14 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (4 : Vertex) [(14 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 125 = true ∨ valuation q 2 = true := by
  rw [value2, value4, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(4 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (14 : Vertex) [(4 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = true ∨ valuation q 4 = true := by
  rw [value3, value4, value5]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ∈ [(10 : Vertex), (12 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (14 : Vertex) [(10 : Vertex), (12 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 126 = true ∨ valuation q 4 = true := by
  rw [value4, value5, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(12 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (10 : Vertex) [(12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 126 = true ∨ valuation q 3 = true := by
  rw [value3, value5, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(10 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (12 : Vertex) [(10 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 127 = true ∨ valuation q 11 = true := by
  rw [value6, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(74 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (67 : Vertex) [(74 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 127 = true ∨ valuation q 7 = true := by
  rw [value6, value7, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(67 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (74 : Vertex) [(67 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 17 = false := by
  rw [value6, value7, value10, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (66 : Vertex) (71 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 17 = false := by
  rw [value7, value10, value12, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (71 : Vertex) (75 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 128 = true ∨ valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 17 = true := by
  rw [value7, value10, value12, value17, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(71 : Vertex), (75 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (66 : Vertex) [(71 : Vertex), (75 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 128 = true ∨ valuation q 6 = true ∨ valuation q 12 = true ∨ valuation q 17 = true := by
  rw [value6, value7, value12, value17, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(66 : Vertex), (75 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (71 : Vertex) [(66 : Vertex), (75 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 128 = true ∨ valuation q 6 = true ∨ valuation q 10 = true ∨ valuation q 17 = true := by
  rw [value6, value7, value10, value17, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(66 : Vertex), (71 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (75 : Vertex) [(66 : Vertex), (71 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 128 = true ∨ valuation q 6 = true ∨ valuation q 10 = true ∨ valuation q 12 = true := by
  rw [value6, value7, value10, value12, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(66 : Vertex), (71 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (83 : Vertex) [(66 : Vertex), (71 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 2 = false ∨ valuation q 9 = false ∨ valuation q 18 = false := by
  rw [value2, value8, value9, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (4 : Vertex) (69 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 2 = false ∨ valuation q 9 = false ∨ valuation q 64 = false := by
  rw [value2, value8, value9, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (4 : Vertex) (69 : Vertex) (324 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 129 = true ∨ valuation q 2 = true ∨ valuation q 18 = true ∨ valuation q 64 = true := by
  rw [value2, value8, value18, value64, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(4 : Vertex), (84 : Vertex), (324 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (69 : Vertex) [(4 : Vertex), (84 : Vertex), (324 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 9 = true := by
  rw [value9, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (69 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 13 = true := by
  rw [value8, value9, value10, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ∈ [(68 : Vertex), (71 : Vertex), (77 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (69 : Vertex) [(68 : Vertex), (71 : Vertex), (77 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 130 = true ∨ valuation q 10 = true ∨ valuation q 13 = true := by
  rw [value9, value10, value13, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(71 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (68 : Vertex) [(71 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 130 = true ∨ valuation q 8 = true ∨ valuation q 13 = true := by
  rw [value8, value9, value13, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(68 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (71 : Vertex) [(68 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E019.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112019
