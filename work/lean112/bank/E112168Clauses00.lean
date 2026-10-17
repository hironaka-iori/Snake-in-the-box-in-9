import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 1 = true := by
  rw [value1, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (18 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ∈ [(19 : Vertex), (22 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (18 : Vertex) [(19 : Vertex), (22 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 115 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(19 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 116 = true := by
  rw [value2, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (19 : Vertex) (18 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 117 = true ∨ valuation q 6 = true := by
  rw [value3, value6, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(30 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 117 = true ∨ valuation q 1 = true := by
  rw [value1, value3, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (30 : Vertex) [(18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 118 = true ∨ valuation q 18 = true := by
  rw [value4, value18, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(88 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (28 : Vertex) [(88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 118 = true ∨ valuation q 5 = true := by
  rw [value4, value5, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(28 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (88 : Vertex) [(28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 119 = true ∨ valuation q 6 = true := by
  rw [value5, value6, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (24 : Vertex) [(30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 119 = true ∨ valuation q 4 = true := by
  rw [value4, value5, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(24 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(24 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 120 = true ∨ valuation q 5 = true := by
  rw [value5, value6, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(28 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (22 : Vertex) [(28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 120 = true ∨ valuation q 3 = true := by
  rw [value3, value6, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (28 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 44 = false := by
  rw [value7, value8, value11, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (67 : Vertex) (74 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value8, value11, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (66 : Vertex) (67 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 11 = false ∨ valuation q 44 = false := by
  rw [value11, value44, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (66 : Vertex) (74 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 121 = true ∨ valuation q 11 = true ∨ valuation q 44 = true := by
  rw [value7, value11, value44, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(74 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (67 : Vertex) [(74 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 121 = true ∨ valuation q 8 = true ∨ valuation q 44 = true := by
  rw [value7, value8, value44, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(67 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (74 : Vertex) [(67 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 121 = true ∨ valuation q 8 = true ∨ valuation q 11 = true := by
  rw [value7, value8, value11, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(67 : Vertex), (74 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (194 : Vertex) [(67 : Vertex), (74 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 122 = true ∨ valuation q 45 = true := by
  rw [value8, value45, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(195 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (66 : Vertex) [(195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 122 = true ∨ valuation q 7 = true := by
  rw [value7, value8, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(66 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (195 : Vertex) [(66 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 123 = true ∨ valuation q 15 = true := by
  rw [value9, value15, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (76 : Vertex) [(84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 123 = true ∨ valuation q 12 = true := by
  rw [value9, value12, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(76 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 48 = false ∨ valuation q 71 = false := by
  rw [value10, value19, value48, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (89 : Vertex) (201 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 124 = true ∨ valuation q 48 = true ∨ valuation q 71 = true := by
  rw [value10, value48, value71, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(201 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (89 : Vertex) [(201 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 124 = true ∨ valuation q 19 = true ∨ valuation q 71 = true := by
  rw [value10, value19, value71, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(89 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (201 : Vertex) [(89 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 124 = true ∨ valuation q 19 = true ∨ valuation q 48 = true := by
  rw [value10, value19, value48, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(89 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (329 : Vertex) [(89 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 20 = false := by
  rw [value7, value11, value13, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (74 : Vertex) (66 : Vertex) (78 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 49 = false := by
  rw [value7, value11, value13, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (74 : Vertex) (66 : Vertex) (78 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 125 = true ∨ valuation q 13 = true ∨ valuation q 20 = true ∨ valuation q 49 = true := by
  rw [value11, value13, value20, value49, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(78 : Vertex), (90 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (66 : Vertex) [(78 : Vertex), (90 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 125 = true ∨ valuation q 7 = true ∨ valuation q 20 = true ∨ valuation q 49 = true := by
  rw [value7, value11, value20, value49, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(66 : Vertex), (90 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (78 : Vertex) [(66 : Vertex), (90 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 125 = true ∨ valuation q 7 = true ∨ valuation q 13 = true ∨ valuation q 20 = true := by
  rw [value7, value11, value13, value20, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(66 : Vertex), (78 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (202 : Vertex) [(66 : Vertex), (78 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 50 = false := by
  rw [value9, value12, value13, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (68 : Vertex) (78 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E168.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112168
