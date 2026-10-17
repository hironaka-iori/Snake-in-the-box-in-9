import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 14 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value14, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 14 = false ∨ valuation q 56 = false ∨ valuation q 116 = false := by
  rw [value14, value54, value56, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 14 = false ∨ valuation q 57 = false ∨ valuation q 116 = false := by
  rw [value14, value54, value57, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value49, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value49, value54, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (217 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 116 = false := by
  rw [value49, value54, value55, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (217 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value49, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 116 = false := by
  rw [value49, value54, value56, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 49 = false ∨ valuation q 57 = false ∨ valuation q 116 = false := by
  rw [value49, value54, value57, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value54, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (217 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 116 = false := by
  rw [value54, value55, value56, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (217 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 116 = false := by
  rw [value54, value55, value57, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (217 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 116 = false := by
  rw [value54, value56, value57, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (218 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 33 = false ∨ valuation q 50 = false := by
  rw [value15, value33, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (153 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 43 = false ∨ valuation q 50 = false := by
  rw [value15, value43, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (201 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value15, value50, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (209 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 50 = false ∨ valuation q 58 = false := by
  rw [value15, value50, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (209 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 54 = false ∨ valuation q 58 = false := by
  rw [value15, value54, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (216 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 33 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value33, value50, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (153 : Vertex) (209 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 43 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value43, value50, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (209 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 50 = false ∨ valuation q 54 = false ∨ valuation q 58 = false := by
  rw [value50, value54, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (209 : Vertex) (216 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 51 = false := by
  rw [value16, value34, value51, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 59 = false := by
  rw [value16, value34, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value16, value51, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 34 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value34, value51, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value44, value51, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (202 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 175 = true ∨ valuation q 34 = true ∨ valuation q 44 = true ∨ valuation q 51 = true ∨ valuation q 54 = true ∨ valuation q 59 = true := by
  rw [value34, value44, value51, value54, value56, value59, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(154 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (90 : Vertex) [(154 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 175 = true ∨ valuation q 16 = true ∨ valuation q 44 = true ∨ valuation q 51 = true ∨ valuation q 54 = true ∨ valuation q 59 = true := by
  rw [value16, value44, value51, value54, value56, value59, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(90 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(90 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 175 = true ∨ valuation q 16 = true ∨ valuation q 34 = true ∨ valuation q 44 = true ∨ valuation q 54 = true ∨ valuation q 59 = true := by
  rw [value16, value34, value44, value54, value56, value59, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(90 : Vertex), (154 : Vertex), (202 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (210 : Vertex) [(90 : Vertex), (154 : Vertex), (202 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 175 = true ∨ valuation q 16 = true ∨ valuation q 34 = true ∨ valuation q 44 = true ∨ valuation q 51 = true ∨ valuation q 54 = true := by
  rw [value16, value34, value44, value51, value54, value56, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(90 : Vertex), (154 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (222 : Vertex) [(90 : Vertex), (154 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 59 = false := by
  rw [value45, value54, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (204 : Vertex) (216 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 176 = true ∨ valuation q 54 = true ∨ valuation q 58 = true ∨ valuation q 59 = true := by
  rw [value54, value57, value58, value59, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(216 : Vertex), (221 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (204 : Vertex) [(216 : Vertex), (221 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E078.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112078
