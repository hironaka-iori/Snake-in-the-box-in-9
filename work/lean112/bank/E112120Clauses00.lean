import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = true ∨ valuation q 49 = true := by
  rw [value1, value3, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ∈ [(15 : Vertex), (267 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (11 : Vertex) [(15 : Vertex), (267 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 3 = false ∨ valuation q 49 = false := by
  rw [value3, value49, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (11 : Vertex) (15 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = true := by
  rw [value1]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 117 = true := by
  rw [value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 6 = true := by
  rw [value2, value6, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (15 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 3 = true := by
  rw [value2, value3, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(15 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (29 : Vertex) [(15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 2 = true := by
  rw [value2, value3, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(13 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (11 : Vertex) [(13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 120 = true ∨ valuation q 56 = true := by
  rw [value4, value56, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(280 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (28 : Vertex) [(280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 6 = true := by
  rw [value5, value6, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (24 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 4 = true := by
  rw [value4, value5, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(24 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (29 : Vertex) [(24 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 25 = false := by
  rw [value2, value5, value6, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (13 : Vertex) (28 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true := by
  rw [value8, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (76 : Vertex) (72 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 78 = false := by
  rw [value9, value10, value15, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (138 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 12 = true ∨ valuation q 79 = true := by
  rw [value10, value12, value79, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(135 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(135 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 9 = true ∨ valuation q 79 = true := by
  rw [value9, value10, value79, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(130 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(130 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 9 = true ∨ valuation q 12 = true := by
  rw [value9, value10, value12, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(130 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (387 : Vertex) [(130 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 21 = false ∨ valuation q 30 = false := by
  rw [value10, value12, value21, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (151 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 21 = false ∨ valuation q 81 = false := by
  rw [value10, value12, value21, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (151 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 30 = false ∨ valuation q 81 = false := by
  rw [value10, value12, value30, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 81 = false := by
  rw [value12, value21, value30, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (151 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false := by
  rw [value13, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 31 = false := by
  rw [value13, value14, value15, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 31 = false := by
  rw [value13, value14, value16, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 31 = false := by
  rw [value13, value15, value16, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 32 = true ∨ valuation q 82 = true := by
  rw [value13, value14, value32, value82, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(136 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (153 : Vertex) [(136 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 22 = true ∨ valuation q 82 = true := by
  rw [value13, value14, value22, value82, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (201 : Vertex) [(136 : Vertex), (153 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value13, value14, value22, value32, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(136 : Vertex), (153 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 23 = false := by
  rw [value9, value15, value17, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (130 : Vertex) (142 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 131 = true ∨ valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 23 = true ∨ valuation q 83 = true := by
  rw [value13, value15, value17, value23, value83, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(136 : Vertex), (142 : Vertex), (154 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (130 : Vertex) [(136 : Vertex), (142 : Vertex), (154 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 132 = true ∨ valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 84 = true := by
  rw [value13, value16, value17, value84, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(136 : Vertex), (142 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (132 : Vertex) [(136 : Vertex), (142 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 86 = false := by
  rw [value15, value16, value17, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (138 : Vertex) (140 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 25 = false := by
  rw [value19, value20, value21, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (148 : Vertex) (151 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E120.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112120
