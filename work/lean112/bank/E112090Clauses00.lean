import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 110 = true ∨ valuation q 39 = true := by
  rw [value1, value39, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(227 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (107 : Vertex) [(227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 111 = true ∨ valuation q 3 = true := by
  rw [value2, value3, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(107 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (122 : Vertex) [(107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 112 = true ∨ valuation q 1 = true := by
  rw [value1, value3, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(99 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (106 : Vertex) [(99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 113 = true ∨ valuation q 10 = true := by
  rw [value4, value10, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (117 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (117 : Vertex) (119 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = true := by
  rw [value5, value6]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ∈ [(119 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (118 : Vertex) [(119 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 5 = true := by
  rw [value5]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 115 = true ∨ valuation q 4 = true := by
  rw [value4, value6, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (119 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(117 : Vertex)] := by decide
  have hg := other_cover q (119 : Vertex) (118 : Vertex) [(117 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 116 = true ∨ valuation q 9 = true := by
  rw [value7, value9, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (120 : Vertex) w → w ∈ region → w ≠ (121 : Vertex) → w ∈ [(122 : Vertex)] := by decide
  have hg := other_cover q (120 : Vertex) (121 : Vertex) [(122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 117 = true ∨ valuation q 7 = true := by
  rw [value7, value8, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(120 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (125 : Vertex) [(120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 118 = true ∨ valuation q 2 = true := by
  rw [value2, value9, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(106 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (120 : Vertex) [(106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 119 = true ∨ valuation q 8 = true := by
  rw [value8, value10, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (117 : Vertex) → w ∈ [(121 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (117 : Vertex) [(121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value11, value13, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (133 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 22 = false := by
  rw [value11, value14, value16, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (133 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 29 = false := by
  rw [value12, value13, value23, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 78 = false := by
  rw [value12, value13, value23, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 29 = false ∨ valuation q 78 = false := by
  rw [value12, value13, value29, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 78 = false := by
  rw [value12, value23, value29, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (146 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 123 = true ∨ valuation q 15 = true ∨ valuation q 19 = true := by
  rw [value14, value15, value19, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(135 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (129 : Vertex) [(135 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 123 = true ∨ valuation q 11 = true ∨ valuation q 19 = true := by
  rw [value11, value14, value19, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (135 : Vertex) [(129 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value13, value14, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 124 = true ∨ valuation q 13 = true ∨ valuation q 20 = true := by
  rw [value13, value15, value20, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(131 : Vertex), (143 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (133 : Vertex) [(131 : Vertex), (143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 124 = true ∨ valuation q 13 = true ∨ valuation q 14 = true := by
  rw [value13, value14, value15, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(131 : Vertex), (133 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (143 : Vertex) [(131 : Vertex), (133 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 125 = true ∨ valuation q 17 = true ∨ valuation q 19 = true := by
  rw [value16, value17, value19, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (129 : Vertex) [(139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 125 = true ∨ valuation q 11 = true ∨ valuation q 19 = true := by
  rw [value11, value16, value19, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (139 : Vertex) [(129 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value13, value16, value17, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 83 = false := by
  rw [value13, value17, value20, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 83 = false := by
  rw [value16, value17, value20, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 127 = true ∨ valuation q 26 = true ∨ valuation q 84 = true := by
  rw [value18, value26, value84, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(156 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (141 : Vertex) [(156 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 127 = true ∨ valuation q 19 = true ∨ valuation q 84 = true := by
  rw [value18, value19, value84, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(141 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (156 : Vertex) [(141 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 127 = true ∨ valuation q 19 = true ∨ valuation q 26 = true := by
  rw [value18, value19, value26, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(141 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (396 : Vertex) [(141 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value14, value16, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 33 = false := by
  rw [value14, value16, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E090.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112090
