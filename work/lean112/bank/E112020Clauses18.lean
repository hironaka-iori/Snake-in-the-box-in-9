import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value75, value103, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value75, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value75, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value75, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value91, value103, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = false ∨ valuation q 103 = false ∨ valuation q 109 = false := by
  rw [value91, value103, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (481 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value91, value103, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value91, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value91, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 91 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value91, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value103, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value103, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value103, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value107, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 57 = false ∨ valuation q 105 = false ∨ valuation q 112 = false := by
  rw [value57, value105, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (483 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 57 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value57, value108, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (489 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value105, value109, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (483 : Vertex) (495 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 108 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value108, value109, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (489 : Vertex) (495 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 105 = true ∨ valuation q 108 = true ∨ valuation q 112 = true ∨ valuation q 120 = true := by
  rw [value105, value108, value109, value112, value120, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(483 : Vertex), (489 : Vertex), (495 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (235 : Vertex) [(483 : Vertex), (489 : Vertex), (495 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 57 = true ∨ valuation q 105 = true ∨ valuation q 108 = true ∨ valuation q 120 = true := by
  rw [value57, value105, value108, value109, value120, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(235 : Vertex), (483 : Vertex), (489 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (495 : Vertex) [(235 : Vertex), (483 : Vertex), (489 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 58 = true ∨ valuation q 107 = true ∨ valuation q 111 = true ∨ valuation q 121 = true := by
  rw [value58, value107, value110, value111, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ∈ [(236 : Vertex), (488 : Vertex), (493 : Vertex), (508 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (492 : Vertex) [(236 : Vertex), (488 : Vertex), (493 : Vertex), (508 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 58 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value58, value107, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 58 = false ∨ valuation q 107 = false ∨ valuation q 121 = false := by
  rw [value58, value107, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (488 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 58 = false ∨ valuation q 111 = false ∨ valuation q 121 = false := by
  rw [value58, value110, value111, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (493 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 107 = false ∨ valuation q 111 = false ∨ valuation q 121 = false := by
  rw [value107, value110, value111, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (488 : Vertex) (493 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 58 = true ∨ valuation q 107 = true ∨ valuation q 121 = true := by
  rw [value58, value107, value110, value121, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(236 : Vertex), (488 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (493 : Vertex) [(236 : Vertex), (488 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 58 = true ∨ valuation q 107 = true ∨ valuation q 111 = true := by
  rw [value58, value107, value110, value111, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(236 : Vertex), (488 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (508 : Vertex) [(236 : Vertex), (488 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 108 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value108, value111, value112, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (489 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 110 = true ∨ valuation q 112 = true ∨ valuation q 122 = true := by
  rw [value110, value111, value112, value122, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(492 : Vertex), (495 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (489 : Vertex) [(492 : Vertex), (495 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 108 = true ∨ valuation q 112 = true ∨ valuation q 122 = true := by
  rw [value108, value111, value112, value122, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(489 : Vertex), (495 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (492 : Vertex) [(489 : Vertex), (495 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 122 = true := by
  rw [value108, value110, value111, value122, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(489 : Vertex), (492 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (495 : Vertex) [(489 : Vertex), (492 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value108, value110, value111, value112, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(489 : Vertex), (492 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (509 : Vertex) [(489 : Vertex), (492 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E020.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112020
