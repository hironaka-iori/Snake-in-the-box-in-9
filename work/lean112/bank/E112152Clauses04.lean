import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 188 = true ∨ valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 107 = true := by
  rw [value65, value67, value68, value107, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(361 : Vertex), (364 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (357 : Vertex) [(361 : Vertex), (364 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 188 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 107 = true := by
  rw [value63, value65, value68, value107, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (364 : Vertex) → w ∈ [(357 : Vertex), (361 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (364 : Vertex) [(357 : Vertex), (361 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 189 = true ∨ valuation q 74 = true := by
  rw [value69, value74, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(376 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (372 : Vertex) [(376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 189 = true ∨ valuation q 70 = true := by
  rw [value69, value70, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(372 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (376 : Vertex) [(372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 190 = true ∨ valuation q 71 = true ∨ valuation q 72 = true := by
  rw [value70, value71, value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(373 : Vertex), (374 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (368 : Vertex) [(373 : Vertex), (374 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 190 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value69, value70, value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(368 : Vertex), (374 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (373 : Vertex) [(368 : Vertex), (374 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 190 = true ∨ valuation q 69 = true ∨ valuation q 71 = true := by
  rw [value69, value70, value71, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (374 : Vertex) → w ∈ [(368 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (374 : Vertex) [(368 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 21 = false ∨ valuation q 63 = false ∨ valuation q 73 = false := by
  rw [value21, value63, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (117 : Vertex) (357 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 21 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value21, value70, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (117 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 21 = false ∨ valuation q 73 = false ∨ valuation q 113 = false := by
  rw [value21, value71, value73, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (117 : Vertex) (375 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 63 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value63, value70, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 63 = false ∨ valuation q 73 = false ∨ valuation q 113 = false := by
  rw [value63, value71, value73, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (375 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 113 = false := by
  rw [value70, value71, value73, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (372 : Vertex) (375 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 64 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value64, value70, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (374 : Vertex) (358 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 64 = false ∨ valuation q 73 = false ∨ valuation q 114 = false := by
  rw [value64, value72, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (374 : Vertex) (358 : Vertex) (375 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 114 = false := by
  rw [value70, value72, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (374 : Vertex) (372 : Vertex) (375 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 71 = true ∨ valuation q 72 = true ∨ valuation q 77 = true ∨ valuation q 115 = true := by
  rw [value71, value72, value73, value77, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ∈ [(373 : Vertex), (374 : Vertex), (383 : Vertex), (503 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (375 : Vertex) [(373 : Vertex), (374 : Vertex), (383 : Vertex), (503 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value71, value72, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (375 : Vertex) (373 : Vertex) (374 : Vertex) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value71, value77, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (375 : Vertex) (373 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 71 = false ∨ valuation q 115 = false := by
  rw [value71, value115, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (375 : Vertex) (373 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 72 = false ∨ valuation q 77 = false := by
  rw [value72, value77, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (375 : Vertex) (374 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 72 = false ∨ valuation q 115 = false := by
  rw [value72, value115, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (375 : Vertex) (374 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 77 = false ∨ valuation q 115 = false := by
  rw [value77, value115, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (375 : Vertex) (383 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 73 = true := by
  rw [value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 193 = true := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 194 = true ∨ valuation q 75 = true := by
  rw [value74, value75, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(378 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (368 : Vertex) [(378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 194 = true ∨ valuation q 69 = true := by
  rw [value69, value74, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(368 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (378 : Vertex) [(368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 195 = true ∨ valuation q 76 = true := by
  rw [value75, value76, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (378 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(379 : Vertex)] := by decide
  have hg := other_cover q (378 : Vertex) (376 : Vertex) [(379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 195 = true ∨ valuation q 74 = true := by
  rw [value74, value75, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (378 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(376 : Vertex)] := by decide
  have hg := other_cover q (378 : Vertex) (379 : Vertex) [(376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 196 = true ∨ valuation q 75 = true ∨ valuation q 77 = true := by
  rw [value75, value76, value77, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(378 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (363 : Vertex) [(378 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 196 = true ∨ valuation q 66 = true ∨ valuation q 77 = true := by
  rw [value66, value76, value77, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(363 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (378 : Vertex) [(363 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 120 = false := by
  rw [value73, value76, value77, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (375 : Vertex) (379 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E152.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112152
