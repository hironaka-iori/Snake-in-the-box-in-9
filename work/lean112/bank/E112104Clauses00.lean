import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 119 = true ∨ valuation q 2 = true ∨ valuation q 6 = true := by
  rw [value1, value2, value6, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(14 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (266 : Vertex) [(14 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 120 = true := by
  rw [value2, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (14 : Vertex) (10 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 8 = true := by
  rw [value3, value4, value5, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ∈ [(35 : Vertex), (37 : Vertex), (49 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (33 : Vertex) [(35 : Vertex), (37 : Vertex), (49 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 5 = false ∨ valuation q 8 = false := by
  rw [value5, value8, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (33 : Vertex) (37 : Vertex) (49 : Vertex) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 4 = true ∨ valuation q 8 = true := by
  rw [value3, value4, value8, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(35 : Vertex), (49 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (37 : Vertex) [(35 : Vertex), (49 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 121 = true ∨ valuation q 4 = true ∨ valuation q 5 = true := by
  rw [value3, value4, value5, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(35 : Vertex), (37 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (49 : Vertex) [(35 : Vertex), (37 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 122 = true := by
  rw [value4, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (35 : Vertex) (33 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 15 = true := by
  rw [value5, value15, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(101 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (33 : Vertex) [(101 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 123 = true ∨ valuation q 3 = true := by
  rw [value3, value5, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(33 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (101 : Vertex) [(33 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 18 = false := by
  rw [value1, value6, value11, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (10 : Vertex) (58 : Vertex) (106 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 11 = true ∨ valuation q 18 = true := by
  rw [value6, value11, value18, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(58 : Vertex), (106 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (10 : Vertex) [(58 : Vertex), (106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 18 = true := by
  rw [value1, value6, value18, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(10 : Vertex), (106 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (58 : Vertex) [(10 : Vertex), (106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 8 = false ∨ valuation q 9 = false := by
  rw [value8, value9, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (48 : Vertex) (49 : Vertex) (50 : Vertex) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 125 = true ∨ valuation q 9 = true := by
  rw [value7, value9, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(50 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (49 : Vertex) [(50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 125 = true ∨ valuation q 8 = true := by
  rw [value7, value8, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(49 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (50 : Vertex) [(49 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 22 = false := by
  rw [value3, value7, value8, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (48 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 126 = true ∨ valuation q 7 = true ∨ valuation q 22 = true := by
  rw [value7, value8, value22, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(48 : Vertex), (113 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (33 : Vertex) [(48 : Vertex), (113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 126 = true ∨ valuation q 3 = true ∨ valuation q 22 = true := by
  rw [value3, value8, value22, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(33 : Vertex), (113 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (48 : Vertex) [(33 : Vertex), (113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value7, value9, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (48 : Vertex) (54 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 10 = true ∨ valuation q 11 = true := by
  rw [value9, value10, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(54 : Vertex), (58 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (48 : Vertex) [(54 : Vertex), (58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 7 = true ∨ valuation q 11 = true := by
  rw [value7, value9, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (54 : Vertex) → w ∈ [(48 : Vertex), (58 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (54 : Vertex) [(48 : Vertex), (58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 10 = true := by
  rw [value10, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (54 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 128 = true ∨ valuation q 25 = true := by
  rw [value10, value25, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (54 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(118 : Vertex)] := by decide
  have hg := other_cover q (54 : Vertex) (50 : Vertex) [(118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 6 = false ∨ valuation q 9 = false := by
  rw [value6, value9, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (58 : Vertex) (42 : Vertex) (50 : Vertex) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 129 = true ∨ valuation q 9 = true := by
  rw [value9, value11, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (58 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(50 : Vertex)] := by decide
  have hg := other_cover q (58 : Vertex) (42 : Vertex) [(50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 129 = true ∨ valuation q 6 = true := by
  rw [value6, value11, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (58 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(42 : Vertex)] := by decide
  have hg := other_cover q (58 : Vertex) (50 : Vertex) [(42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 17 = true := by
  rw [value12, value13, value14, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ∈ [(98 : Vertex), (100 : Vertex), (104 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (96 : Vertex) [(98 : Vertex), (100 : Vertex), (104 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 17 = false := by
  rw [value12, value13, value14, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (98 : Vertex) (100 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 14 = true ∨ valuation q 17 = true := by
  rw [value12, value14, value17, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (98 : Vertex) → w ∈ [(100 : Vertex), (104 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (98 : Vertex) [(100 : Vertex), (104 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 17 = true := by
  rw [value12, value13, value17, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (100 : Vertex) → w ∈ [(98 : Vertex), (104 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (100 : Vertex) [(98 : Vertex), (104 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 14 = true := by
  rw [value12, value13, value14, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(98 : Vertex), (100 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (104 : Vertex) [(98 : Vertex), (100 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 16 = true ∨ valuation q 18 = true := by
  rw [value13, value16, value18, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(102 : Vertex), (106 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (96 : Vertex) [(102 : Vertex), (106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E104.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112104
