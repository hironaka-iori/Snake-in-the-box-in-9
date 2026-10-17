import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 112 = true := by
  rw [value1, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (2 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true ∨ valuation q 3 = true ∨ valuation q 44 = true := by
  rw [value1, value2, value3, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (6 : Vertex), (258 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (2 : Vertex) [(0 : Vertex), (6 : Vertex), (258 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 113 = true ∨ valuation q 1 = true ∨ valuation q 44 = true := by
  rw [value1, value2, value44, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(0 : Vertex), (258 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (6 : Vertex) [(0 : Vertex), (258 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 113 = true ∨ valuation q 1 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(0 : Vertex), (6 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (258 : Vertex) [(0 : Vertex), (6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 114 = true ∨ valuation q 47 = true := by
  rw [value3, value47, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(262 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (2 : Vertex) [(262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 114 = true ∨ valuation q 2 = true := by
  rw [value2, value3, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(2 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (262 : Vertex) [(2 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 115 = true ∨ valuation q 40 = true := by
  rw [value4, value40, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(229 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (109 : Vertex) [(229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 116 = true ∨ valuation q 6 = true := by
  rw [value5, value6, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (124 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 117 = true ∨ valuation q 4 = true := by
  rw [value4, value6, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(101 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (108 : Vertex) [(101 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 10 = true := by
  rw [value7, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (123 : Vertex) w → w ∈ region → w ∈ [(127 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (123 : Vertex) [(127 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 7 = true := by
  rw [value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 119 = true ∨ valuation q 5 = true := by
  rw [value5, value8, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(108 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (126 : Vertex) [(108 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 120 = true ∨ valuation q 8 = true := by
  rw [value8, value9, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (127 : Vertex) → w ∈ [(124 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (127 : Vertex) [(124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 121 = true ∨ valuation q 9 = true := by
  rw [value9, value10, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (127 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(126 : Vertex)] := by decide
  have hg := other_cover q (127 : Vertex) (123 : Vertex) [(126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value11, value12, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (133 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 122 = true ∨ valuation q 14 = true ∨ valuation q 16 = true := by
  rw [value11, value14, value16, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(133 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (131 : Vertex) [(133 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 122 = true ∨ valuation q 12 = true ∨ valuation q 16 = true := by
  rw [value11, value12, value16, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(131 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (133 : Vertex) [(131 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 122 = true ∨ valuation q 12 = true ∨ valuation q 14 = true := by
  rw [value11, value12, value14, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(131 : Vertex), (133 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (137 : Vertex) [(131 : Vertex), (133 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 12 = true := by
  rw [value12, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (131 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value11, value12, value15, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ∈ [(129 : Vertex), (135 : Vertex), (139 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (131 : Vertex) [(129 : Vertex), (135 : Vertex), (139 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 123 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value12, value15, value18, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (129 : Vertex) [(135 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 123 = true ∨ valuation q 11 = true ∨ valuation q 18 = true := by
  rw [value11, value12, value18, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(129 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(129 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 123 = true ∨ valuation q 11 = true ∨ valuation q 15 = true := by
  rw [value11, value12, value15, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(129 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (139 : Vertex) [(129 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value13, value14, value22, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (148 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 81 = false := by
  rw [value13, value14, value22, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (148 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 30 = false ∨ valuation q 81 = false := by
  rw [value13, value14, value30, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (196 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 81 = false := by
  rw [value13, value22, value30, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (148 : Vertex) (196 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 124 = true ∨ valuation q 14 = true ∨ valuation q 22 = true ∨ valuation q 81 = true := by
  rw [value13, value14, value22, value81, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(133 : Vertex), (148 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (196 : Vertex) [(133 : Vertex), (148 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 82 = false := by
  rw [value11, value13, value14, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (132 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 82 = false := by
  rw [value11, value14, value15, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (135 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = false ∨ valuation q 31 = false ∨ valuation q 82 = false := by
  rw [value11, value14, value31, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 82 = false := by
  rw [value13, value14, value15, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E161.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112161
