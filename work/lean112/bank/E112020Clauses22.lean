import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 109 = false ∨ valuation q 124 = false := by
  rw [value68, value109, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (491 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value68, value116, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (499 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 83 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value83, value99, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 83 = false ∨ valuation q 99 = false ∨ valuation q 116 = false := by
  rw [value83, value99, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 83 = false ∨ valuation q 99 = false ∨ valuation q 124 = false := by
  rw [value83, value99, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (443 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 83 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value83, value109, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 83 = false ∨ valuation q 109 = false ∨ valuation q 124 = false := by
  rw [value83, value109, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (491 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 83 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value83, value116, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (499 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 99 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value99, value109, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (443 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 99 = false ∨ valuation q 109 = false ∨ valuation q 124 = false := by
  rw [value99, value109, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (443 : Vertex) (491 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 109 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value109, value116, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (491 : Vertex) (499 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 117 = false ∨ valuation q 119 = false := by
  rw [value110, value117, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (492 : Vertex) (500 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value110, value119, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (492 : Vertex) (504 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value110, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (492 : Vertex) (509 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value117, value119, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (500 : Vertex) (504 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 119 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value119, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (504 : Vertex) (509 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 122 = true ∨ valuation q 123 = true := by
  rw [value117, value119, value121, value122, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(500 : Vertex), (504 : Vertex), (509 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (492 : Vertex) [(500 : Vertex), (504 : Vertex), (509 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 110 = true ∨ valuation q 119 = true ∨ valuation q 122 = true ∨ valuation q 123 = true := by
  rw [value110, value119, value121, value122, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(492 : Vertex), (504 : Vertex), (509 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (500 : Vertex) [(492 : Vertex), (504 : Vertex), (509 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 123 = true := by
  rw [value110, value117, value121, value122, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(492 : Vertex), (500 : Vertex), (509 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (504 : Vertex) [(492 : Vertex), (500 : Vertex), (509 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 123 = true := by
  rw [value110, value117, value119, value121, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(492 : Vertex), (500 : Vertex), (504 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (509 : Vertex) [(492 : Vertex), (500 : Vertex), (504 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 122 = true := by
  rw [value110, value117, value119, value121, value122, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(492 : Vertex), (500 : Vertex), (504 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (510 : Vertex) [(492 : Vertex), (500 : Vertex), (504 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 84 = false ∨ valuation q 100 = false := by
  rw [value69, value84, value100, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 84 = false ∨ valuation q 111 = false := by
  rw [value69, value84, value111, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 84 = false ∨ valuation q 121 = false := by
  rw [value69, value84, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 84 = false ∨ valuation q 124 = false := by
  rw [value69, value84, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 100 = false ∨ valuation q 111 = false := by
  rw [value69, value100, value111, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (445 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 100 = false ∨ valuation q 121 = false := by
  rw [value69, value100, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (445 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 100 = false ∨ valuation q 124 = false := by
  rw [value69, value100, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (445 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 111 = false ∨ valuation q 121 = false := by
  rw [value69, value111, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (493 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value69, value111, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (493 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 69 = false ∨ valuation q 121 = false ∨ valuation q 124 = false := by
  rw [value69, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (508 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 84 = false ∨ valuation q 100 = false ∨ valuation q 111 = false := by
  rw [value84, value100, value111, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (445 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E020.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112020
