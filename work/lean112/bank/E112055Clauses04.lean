import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 85 = false := by
  rw [value12, value14, value15, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (22 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 85 = false := by
  rw [value12, value15, value20, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (31 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value12, value15, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (151 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value13, value14, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (21 : Vertex) (22 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 85 = false := by
  rw [value13, value14, value15, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (21 : Vertex) (22 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 85 = false := by
  rw [value13, value15, value20, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (21 : Vertex) (31 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value13, value15, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (21 : Vertex) (151 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 20 = false ∨ valuation q 52 = false := by
  rw [value14, value15, value20, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (22 : Vertex) (31 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 20 = false ∨ valuation q 85 = false := by
  rw [value14, value15, value20, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (22 : Vertex) (31 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value14, value15, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (22 : Vertex) (151 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 20 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value15, value20, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (31 : Vertex) (151 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 16 = true := by
  rw [value16, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (25 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 10 = true ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 87 = true := by
  rw [value10, value16, value17, value19, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ∈ [(17 : Vertex), (27 : Vertex), (29 : Vertex), (281 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (25 : Vertex) [(17 : Vertex), (27 : Vertex), (29 : Vertex), (281 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 10 = false ∨ valuation q 87 = false := by
  rw [value10, value87, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (25 : Vertex) (17 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 17 = false ∨ valuation q 87 = false := by
  rw [value17, value87, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (25 : Vertex) (27 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 87 = true := by
  rw [value16, value17, value19, value87, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(27 : Vertex), (29 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (17 : Vertex) [(27 : Vertex), (29 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 10 = true ∨ valuation q 19 = true ∨ valuation q 87 = true := by
  rw [value10, value16, value19, value87, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(17 : Vertex), (29 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (27 : Vertex) [(17 : Vertex), (29 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 10 = true ∨ valuation q 17 = true ∨ valuation q 87 = true := by
  rw [value10, value16, value17, value87, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(17 : Vertex), (27 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (29 : Vertex) [(17 : Vertex), (27 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 10 = true ∨ valuation q 17 = true ∨ valuation q 19 = true := by
  rw [value10, value16, value17, value19, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(17 : Vertex), (27 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (281 : Vertex) [(17 : Vertex), (27 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value12, value16, value17, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (19 : Vertex) (25 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 89 = false := by
  rw [value12, value16, value17, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (19 : Vertex) (25 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 89 = false := by
  rw [value12, value17, value20, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (19 : Vertex) (31 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 89 = false := by
  rw [value16, value17, value20, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (25 : Vertex) (31 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 145 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 89 = true := by
  rw [value16, value17, value20, value89, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(25 : Vertex), (31 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (19 : Vertex) [(25 : Vertex), (31 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 145 = true ∨ valuation q 12 = true ∨ valuation q 20 = true ∨ valuation q 89 = true := by
  rw [value12, value17, value20, value89, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(19 : Vertex), (31 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (25 : Vertex) [(19 : Vertex), (31 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 145 = true ∨ valuation q 12 = true ∨ valuation q 16 = true ∨ valuation q 89 = true := by
  rw [value12, value16, value17, value89, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(19 : Vertex), (25 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (31 : Vertex) [(19 : Vertex), (25 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 7 = true ∨ valuation q 19 = true ∨ valuation q 36 = true ∨ valuation q 90 = true := by
  rw [value7, value18, value19, value36, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ∈ [(12 : Vertex), (29 : Vertex), (92 : Vertex), (284 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (28 : Vertex) [(12 : Vertex), (29 : Vertex), (92 : Vertex), (284 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 7 = false ∨ valuation q 19 = false ∨ valuation q 36 = false := by
  rw [value7, value18, value19, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (12 : Vertex) (29 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 36 = false ∨ valuation q 90 = false := by
  rw [value18, value19, value36, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (29 : Vertex) (92 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 19 = true ∨ valuation q 36 = true ∨ valuation q 90 = true := by
  rw [value18, value19, value36, value90, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(29 : Vertex), (92 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (12 : Vertex) [(29 : Vertex), (92 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 7 = true ∨ valuation q 36 = true ∨ valuation q 90 = true := by
  rw [value7, value18, value36, value90, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(12 : Vertex), (92 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (29 : Vertex) [(12 : Vertex), (92 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 7 = true ∨ valuation q 19 = true ∨ valuation q 90 = true := by
  rw [value7, value18, value19, value90, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(12 : Vertex), (29 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (92 : Vertex) [(12 : Vertex), (29 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E055.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112055
