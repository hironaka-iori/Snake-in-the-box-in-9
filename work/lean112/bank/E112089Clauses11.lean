import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 51 = true := by
  rw [value51, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (152 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 40 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 74 = true := by
  rw [value40, value51, value52, value53, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ∈ [(136 : Vertex), (153 : Vertex), (154 : Vertex), (216 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (152 : Vertex) [(136 : Vertex), (153 : Vertex), (154 : Vertex), (216 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 74 = true := by
  rw [value51, value52, value53, value74, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(153 : Vertex), (154 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (136 : Vertex) [(153 : Vertex), (154 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 40 = true ∨ valuation q 53 = true ∨ valuation q 74 = true := by
  rw [value40, value51, value53, value74, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(136 : Vertex), (154 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (153 : Vertex) [(136 : Vertex), (154 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 40 = true ∨ valuation q 52 = true ∨ valuation q 74 = true := by
  rw [value40, value51, value52, value74, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (154 : Vertex) [(136 : Vertex), (153 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 40 = true ∨ valuation q 52 = true ∨ valuation q 53 = true := by
  rw [value40, value51, value52, value53, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (216 : Vertex) [(136 : Vertex), (153 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 41 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value41, value46, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (145 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 41 = false ∨ valuation q 46 = false ∨ valuation q 54 = false := by
  rw [value41, value46, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (145 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 41 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value41, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (152 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value46, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (145 : Vertex) (152 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 41 = true ∨ valuation q 46 = true ∨ valuation q 54 = true := by
  rw [value41, value46, value52, value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(137 : Vertex), (145 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (152 : Vertex) [(137 : Vertex), (145 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value42, value51, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (152 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 75 = false := by
  rw [value42, value51, value53, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (152 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 42 = false ∨ valuation q 54 = false ∨ valuation q 75 = false := by
  rw [value42, value53, value54, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 75 = false := by
  rw [value51, value53, value54, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (152 : Vertex) (155 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 51 = true ∨ valuation q 54 = true ∨ valuation q 75 = true := by
  rw [value51, value53, value54, value75, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(152 : Vertex), (155 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (138 : Vertex) [(152 : Vertex), (155 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 42 = true ∨ valuation q 54 = true ∨ valuation q 75 = true := by
  rw [value42, value53, value54, value75, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(138 : Vertex), (155 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (152 : Vertex) [(138 : Vertex), (155 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 42 = true ∨ valuation q 51 = true ∨ valuation q 75 = true := by
  rw [value42, value51, value53, value75, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(138 : Vertex), (152 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (155 : Vertex) [(138 : Vertex), (152 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 54 = true := by
  rw [value54, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (155 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 43 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 55 = true := by
  rw [value43, value52, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ∈ [(139 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (155 : Vertex) [(139 : Vertex), (153 : Vertex), (154 : Vertex), (159 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 43 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value43, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (139 : Vertex) (153 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 43 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value43, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (139 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value52, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (153 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 55 = true := by
  rw [value52, value53, value54, value55, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(153 : Vertex), (154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (139 : Vertex) [(153 : Vertex), (154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 43 = true ∨ valuation q 53 = true ∨ valuation q 55 = true := by
  rw [value43, value53, value54, value55, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(139 : Vertex), (154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (153 : Vertex) [(139 : Vertex), (154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 43 = true ∨ valuation q 52 = true ∨ valuation q 55 = true := by
  rw [value43, value52, value54, value55, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(139 : Vertex), (153 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (154 : Vertex) [(139 : Vertex), (153 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 43 = true ∨ valuation q 52 = true ∨ valuation q 53 = true := by
  rw [value43, value52, value53, value54, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(139 : Vertex), (153 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (159 : Vertex) [(139 : Vertex), (153 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value45, value50, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (143 : Vertex) (151 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 179 = true ∨ valuation q 50 = true ∨ valuation q 54 = true := by
  rw [value50, value54, value55, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(151 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (143 : Vertex) [(151 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 179 = true ∨ valuation q 45 = true ∨ valuation q 54 = true := by
  rw [value45, value54, value55, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(143 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (151 : Vertex) [(143 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 179 = true ∨ valuation q 45 = true ∨ valuation q 50 = true := by
  rw [value45, value50, value55, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(143 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (155 : Vertex) [(143 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 36 = false ∨ valuation q 108 = false := by
  rw [value19, value36, value56, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E089.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112089
