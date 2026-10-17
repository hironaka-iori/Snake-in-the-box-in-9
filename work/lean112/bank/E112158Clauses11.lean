import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 35 = false ∨ valuation q 51 = false ∨ valuation q 55 = false := by
  rw [value35, value51, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (194 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 35 = false ∨ valuation q 51 = false ∨ valuation q 59 = false := by
  rw [value35, value51, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (194 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 35 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value35, value55, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value51, value55, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 35 = true ∨ valuation q 55 = true ∨ valuation q 59 = true := by
  rw [value35, value55, value56, value59, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(138 : Vertex), (200 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (194 : Vertex) [(138 : Vertex), (200 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 35 = true ∨ valuation q 51 = true ∨ valuation q 59 = true := by
  rw [value35, value51, value56, value59, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(138 : Vertex), (194 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (200 : Vertex) [(138 : Vertex), (194 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 58 = false := by
  rw [value53, value55, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value53, value55, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 68 = false := by
  rw [value53, value55, value57, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (200 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value53, value57, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 58 = false ∨ valuation q 68 = false := by
  rw [value53, value57, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 59 = false ∨ valuation q 68 = false := by
  rw [value53, value57, value59, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value55, value57, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (200 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 68 = false := by
  rw [value55, value57, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (200 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 55 = false ∨ valuation q 59 = false ∨ valuation q 68 = false := by
  rw [value55, value57, value59, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (200 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 68 = false := by
  rw [value57, value58, value59, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (205 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 175 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 58 = true ∨ valuation q 59 = true := by
  rw [value53, value55, value57, value58, value59, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(196 : Vertex), (200 : Vertex), (205 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (220 : Vertex) [(196 : Vertex), (200 : Vertex), (205 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 37 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value37, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (141 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 37 = false ∨ valuation q 57 = false ∨ valuation q 69 = false := by
  rw [value37, value57, value58, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (141 : Vertex) (204 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 37 = false ∨ valuation q 60 = false ∨ valuation q 69 = false := by
  rw [value37, value58, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (141 : Vertex) (207 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 69 = false := by
  rw [value57, value58, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (204 : Vertex) (207 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 57 = true ∨ valuation q 60 = true ∨ valuation q 69 = true := by
  rw [value57, value58, value60, value69, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(204 : Vertex), (207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (141 : Vertex) [(204 : Vertex), (207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 37 = true ∨ valuation q 60 = true ∨ valuation q 69 = true := by
  rw [value37, value58, value60, value69, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(141 : Vertex), (207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (204 : Vertex) [(141 : Vertex), (207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 37 = true ∨ valuation q 57 = true ∨ valuation q 69 = true := by
  rw [value37, value57, value58, value69, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(141 : Vertex), (204 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (207 : Vertex) [(141 : Vertex), (204 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 37 = true ∨ valuation q 57 = true ∨ valuation q 60 = true := by
  rw [value37, value57, value58, value60, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(141 : Vertex), (204 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (221 : Vertex) [(141 : Vertex), (204 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 38 = false ∨ valuation q 56 = false := by
  rw [value18, value38, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 38 = false ∨ valuation q 57 = false := by
  rw [value18, value38, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 38 = false ∨ valuation q 70 = false := by
  rw [value18, value38, value59, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value18, value56, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (202 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 70 = false ∨ valuation q 108 = false := by
  rw [value18, value59, value70, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value56, value57, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (202 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 70 = false := by
  rw [value56, value59, value60, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (202 : Vertex) (207 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E158.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112158
