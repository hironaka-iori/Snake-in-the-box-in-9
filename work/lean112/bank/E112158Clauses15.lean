import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 44 = false ∨ valuation q 54 = false ∨ valuation q 71 = false := by
  rw [value44, value54, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (199 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 44 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value44, value63, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (211 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 44 = false ∨ valuation q 63 = false ∨ valuation q 71 = false := by
  rw [value44, value63, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (211 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 44 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value44, value65, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (213 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 54 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value54, value63, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (211 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 54 = false ∨ valuation q 63 = false ∨ valuation q 71 = false := by
  rw [value54, value63, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (211 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 54 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value54, value65, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value63, value65, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (211 : Vertex) (213 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 24 = true ∨ valuation q 54 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 71 = true := by
  rw [value24, value54, value63, value65, value66, value71, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(87 : Vertex), (199 : Vertex), (211 : Vertex), (213 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (151 : Vertex) [(87 : Vertex), (199 : Vertex), (211 : Vertex), (213 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 24 = true ∨ valuation q 44 = true ∨ valuation q 54 = true ∨ valuation q 65 = true ∨ valuation q 71 = true := by
  rw [value24, value44, value54, value65, value66, value71, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(87 : Vertex), (151 : Vertex), (199 : Vertex), (213 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (211 : Vertex) [(87 : Vertex), (151 : Vertex), (199 : Vertex), (213 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 63 = false ∨ valuation q 71 = false ∨ valuation q 117 = false := by
  rw [value63, value67, value71, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (211 : Vertex) (223 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 71 = true ∨ valuation q 117 = true := by
  rw [value67, value71, value117, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(223 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (211 : Vertex) [(223 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 63 = true ∨ valuation q 71 = true := by
  rw [value63, value67, value71, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(211 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (475 : Vertex) [(211 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 64 = true ∨ valuation q 69 = true ∨ valuation q 70 = true := by
  rw [value64, value68, value69, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(212 : Vertex), (221 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (204 : Vertex) [(212 : Vertex), (221 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 70 = true := by
  rw [value57, value68, value69, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(204 : Vertex), (221 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (212 : Vertex) [(204 : Vertex), (221 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 57 = true ∨ valuation q 64 = true ∨ valuation q 70 = true := by
  rw [value57, value64, value68, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(204 : Vertex), (212 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(204 : Vertex), (212 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 57 = true ∨ valuation q 64 = true ∨ valuation q 69 = true := by
  rw [value57, value64, value68, value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(204 : Vertex), (212 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (222 : Vertex) [(204 : Vertex), (212 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 48 = false ∨ valuation q 58 = false := by
  rw [value28, value48, value58, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (157 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 48 = false ∨ valuation q 65 = false := by
  rw [value28, value48, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (157 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 48 = false ∨ valuation q 68 = false := by
  rw [value28, value48, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (157 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 48 = false ∨ valuation q 71 = false := by
  rw [value28, value48, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (157 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 48 = false ∨ valuation q 118 = false := by
  rw [value28, value48, value69, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (157 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 65 = false := by
  rw [value28, value58, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (205 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 68 = false := by
  rw [value28, value58, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 71 = false := by
  rw [value28, value58, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (205 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 118 = false := by
  rw [value28, value58, value69, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (205 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value28, value65, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (213 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value28, value65, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (213 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 65 = false ∨ valuation q 118 = false := by
  rw [value28, value65, value69, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (213 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value28, value68, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (220 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 68 = false ∨ valuation q 118 = false := by
  rw [value28, value68, value69, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (220 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 28 = false ∨ valuation q 71 = false ∨ valuation q 118 = false := by
  rw [value28, value69, value71, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (223 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E158.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112158
