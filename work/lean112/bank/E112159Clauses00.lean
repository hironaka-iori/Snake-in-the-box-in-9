import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 119 = true := by
  rw [value1, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (2 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (6 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (2 : Vertex) [(0 : Vertex), (6 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 120 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (6 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 53 = true := by
  rw [value3, value53, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(262 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (2 : Vertex) [(262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 2 = true := by
  rw [value2, value3, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(2 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (262 : Vertex) [(2 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 122 = true ∨ valuation q 34 = true := by
  rw [value4, value34, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(229 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (109 : Vertex) [(229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 122 = true ∨ valuation q 6 = true := by
  rw [value4, value6, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (229 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 40 = false := by
  rw [value5, value6, value8, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (108 : Vertex) (109 : Vertex) (124 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 8 = true ∨ valuation q 40 = true := by
  rw [value5, value8, value40, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(124 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (109 : Vertex) [(124 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 6 = true ∨ valuation q 40 = true := by
  rw [value5, value6, value40, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(109 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (124 : Vertex) [(109 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 6 = true ∨ valuation q 8 = true := by
  rw [value5, value6, value8, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(109 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (236 : Vertex) [(109 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 9 = false := by
  rw [value4, value5, value6, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (109 : Vertex) (101 : Vertex) (108 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 41 = false := by
  rw [value4, value6, value9, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (109 : Vertex) (101 : Vertex) (125 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 5 = true ∨ valuation q 9 = true ∨ valuation q 41 = true := by
  rw [value5, value6, value9, value41, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(108 : Vertex), (125 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (101 : Vertex) [(108 : Vertex), (125 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 41 = true := by
  rw [value4, value6, value9, value41, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(101 : Vertex), (125 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (108 : Vertex) [(101 : Vertex), (125 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 11 = true := by
  rw [value7, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (123 : Vertex) w → w ∈ region → w ∈ [(127 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (123 : Vertex) [(127 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 7 = true := by
  rw [value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 51 = false := by
  rw [value5, value8, value10, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (124 : Vertex) (108 : Vertex) (126 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value6, value8, value9, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (109 : Vertex) (124 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 6 = false ∨ valuation q 11 = false ∨ valuation q 83 = false := by
  rw [value6, value9, value11, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (109 : Vertex) (127 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 52 = false := by
  rw [value8, value10, value11, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (124 : Vertex) (127 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 128 = true ∨ valuation q 8 = true ∨ valuation q 52 = true := by
  rw [value8, value10, value52, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (127 : Vertex) → w ∈ [(124 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (127 : Vertex) [(124 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 10 = false := by
  rw [value7, value9, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (123 : Vertex) (125 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 129 = true ∨ valuation q 9 = true ∨ valuation q 10 = true := by
  rw [value9, value10, value11, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (127 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(125 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (127 : Vertex) (123 : Vertex) [(125 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 16 = true ∨ valuation q 22 = true := by
  rw [value12, value16, value22, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(168 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (162 : Vertex) [(168 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 22 = true := by
  rw [value12, value13, value22, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(162 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (168 : Vertex) [(162 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 16 = true := by
  rw [value12, value13, value16, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(162 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (176 : Vertex) [(162 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 24 = false := by
  rw [value12, value13, value15, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (166 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 15 = true ∨ valuation q 24 = true := by
  rw [value13, value15, value24, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(166 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (160 : Vertex) [(166 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 26 = false ∨ valuation q 34 = false := by
  rw [value14, value19, value26, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (173 : Vertex) (181 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 132 = true ∨ valuation q 26 = true ∨ valuation q 34 = true := by
  rw [value14, value26, value34, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(181 : Vertex), (229 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (173 : Vertex) [(181 : Vertex), (229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 132 = true ∨ valuation q 19 = true ∨ valuation q 34 = true := by
  rw [value14, value19, value34, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(173 : Vertex), (229 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (181 : Vertex) [(173 : Vertex), (229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E159.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112159
