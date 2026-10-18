import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 86 = false ∨ valuation q 101 = false := by
  rw [value70, value86, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 86 = false ∨ valuation q 108 = false := by
  rw [value70, value86, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (424 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 86 = false ∨ valuation q 109 = false := by
  rw [value70, value86, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (424 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 86 = false ∨ valuation q 111 = false := by
  rw [value70, value86, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (424 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value70, value101, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (480 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value70, value101, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (480 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 101 = false ∨ valuation q 111 = false := by
  rw [value70, value101, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (480 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value70, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (489 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value70, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value70, value107, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 86 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value86, value101, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 86 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value86, value101, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 86 = false ∨ valuation q 101 = false ∨ valuation q 111 = false := by
  rw [value86, value101, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 86 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value86, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (489 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 86 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value86, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 86 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value86, value107, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value101, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (480 : Vertex) (489 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value101, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (480 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value101, value107, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (480 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value107, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (489 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 230 = true ∨ valuation q 34 = true ∨ valuation q 86 = true ∨ valuation q 101 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 111 = true := by
  rw [value34, value86, value101, value107, value108, value109, value111, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(232 : Vertex), (424 : Vertex), (480 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (360 : Vertex) [(232 : Vertex), (424 : Vertex), (480 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 230 = true ∨ valuation q 34 = true ∨ valuation q 70 = true ∨ valuation q 86 = true ∨ valuation q 101 = true ∨ valuation q 108 = true ∨ valuation q 111 = true := by
  rw [value34, value70, value86, value101, value107, value108, value111, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(232 : Vertex), (360 : Vertex), (424 : Vertex), (480 : Vertex), (489 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (490 : Vertex) [(232 : Vertex), (360 : Vertex), (424 : Vertex), (480 : Vertex), (489 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 35 = false ∨ valuation q 71 = false ∨ valuation q 102 = false := by
  rw [value35, value71, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (361 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 35 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value35, value102, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 35 = false ∨ valuation q 107 = false ∨ valuation q 119 = false := by
  rw [value35, value107, value108, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 71 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value71, value107, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 71 = false ∨ valuation q 107 = false ∨ valuation q 119 = false := by
  rw [value71, value107, value108, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 107 = false ∨ valuation q 110 = false ∨ valuation q 119 = false := by
  rw [value107, value108, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (491 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 107 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value107, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (488 : Vertex) (491 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 107 = false ∨ valuation q 110 = false ∨ valuation q 120 = false := by
  rw [value107, value109, value110, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (488 : Vertex) (491 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 107 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value107, value109, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (488 : Vertex) (494 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 232 = true ∨ valuation q 103 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value103, value107, value109, value110, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(482 : Vertex), (488 : Vertex), (491 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (506 : Vertex) [(482 : Vertex), (488 : Vertex), (491 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block16 (q : Snake 81) (h : Conditions q) : B112E097.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112097
