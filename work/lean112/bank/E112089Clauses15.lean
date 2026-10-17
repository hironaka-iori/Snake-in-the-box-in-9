import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 23 = false ∨ valuation q 63 = false ∨ valuation q 112 = false := by
  rw [value23, value62, value63, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (201 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 23 = false ∨ valuation q 65 = false ∨ valuation q 112 = false := by
  rw [value23, value62, value65, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (204 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 23 = false ∨ valuation q 74 = false ∨ valuation q 112 = false := by
  rw [value23, value62, value74, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (216 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 40 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value40, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (136 : Vertex) (201 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 40 = false ∨ valuation q 63 = false ∨ valuation q 74 = false := by
  rw [value40, value62, value63, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (136 : Vertex) (201 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 40 = false ∨ valuation q 63 = false ∨ valuation q 112 = false := by
  rw [value40, value62, value63, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (136 : Vertex) (201 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 40 = false ∨ valuation q 74 = false ∨ valuation q 112 = false := by
  rw [value40, value62, value74, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (136 : Vertex) (216 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 74 = false := by
  rw [value62, value63, value65, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (201 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 74 = false ∨ valuation q 112 = false := by
  rw [value62, value63, value74, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (201 : Vertex) (216 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 74 = false ∨ valuation q 112 = false := by
  rw [value62, value65, value74, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (204 : Vertex) (216 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 40 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 74 = true ∨ valuation q 112 = true := by
  rw [value40, value62, value63, value65, value74, value112, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(136 : Vertex), (201 : Vertex), (204 : Vertex), (216 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (72 : Vertex) [(136 : Vertex), (201 : Vertex), (204 : Vertex), (216 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 23 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 74 = true ∨ valuation q 112 = true := by
  rw [value23, value62, value63, value65, value74, value112, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(72 : Vertex), (201 : Vertex), (204 : Vertex), (216 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (136 : Vertex) [(72 : Vertex), (201 : Vertex), (204 : Vertex), (216 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 23 = true ∨ valuation q 40 = true ∨ valuation q 65 = true ∨ valuation q 74 = true ∨ valuation q 112 = true := by
  rw [value23, value40, value62, value65, value74, value112, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(72 : Vertex), (136 : Vertex), (204 : Vertex), (216 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(72 : Vertex), (136 : Vertex), (204 : Vertex), (216 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 23 = true ∨ valuation q 40 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 112 = true := by
  rw [value23, value40, value62, value63, value65, value112, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(72 : Vertex), (136 : Vertex), (201 : Vertex), (204 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (216 : Vertex) [(72 : Vertex), (136 : Vertex), (201 : Vertex), (204 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 23 = true ∨ valuation q 40 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 74 = true := by
  rw [value23, value40, value62, value63, value65, value74, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(72 : Vertex), (136 : Vertex), (201 : Vertex), (204 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (456 : Vertex) [(72 : Vertex), (136 : Vertex), (201 : Vertex), (204 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 41 = false ∨ valuation q 56 = false := by
  rw [value24, value41, value56, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (137 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 41 = false ∨ valuation q 62 = false := by
  rw [value24, value41, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (137 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 41 = false ∨ valuation q 64 = false := by
  rw [value24, value41, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (137 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 41 = false ∨ valuation q 66 = false := by
  rw [value24, value41, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (137 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 41 = false ∨ valuation q 113 = false := by
  rw [value24, value41, value63, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (137 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 62 = false := by
  rw [value24, value56, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 64 = false := by
  rw [value24, value56, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (193 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 66 = false := by
  rw [value24, value56, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 113 = false := by
  rw [value24, value56, value63, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (193 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value24, value62, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value24, value62, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 62 = false ∨ valuation q 113 = false := by
  rw [value24, value62, value63, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (200 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value24, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 64 = false ∨ valuation q 113 = false := by
  rw [value24, value63, value64, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (203 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 24 = false ∨ valuation q 66 = false ∨ valuation q 113 = false := by
  rw [value24, value63, value66, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (73 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 56 = false ∨ valuation q 62 = false := by
  rw [value41, value56, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 41 = false ∨ valuation q 56 = false ∨ valuation q 64 = false := by
  rw [value41, value56, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E089.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112089
