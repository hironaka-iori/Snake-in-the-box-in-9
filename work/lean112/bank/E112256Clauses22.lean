import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value111, value113, value114, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (473 : Vertex) (476 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 91 = true := by
  rw [value91, value115, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (476 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 94 = true ∨ valuation q 127 = true := by
  rw [value94, value116, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ∈ [(367 : Vertex), (511 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (495 : Vertex) [(367 : Vertex), (511 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 243 = true ∨ valuation q 127 = true := by
  rw [value116, value127, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(511 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (367 : Vertex) [(511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 243 = true ∨ valuation q 94 = true := by
  rw [value94, value116, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(367 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (511 : Vertex) [(367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 63 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value63, value106, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (496 : Vertex) (240 : Vertex) (464 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 63 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value63, value117, value118, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (496 : Vertex) (240 : Vertex) (498 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 106 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value106, value117, value118, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (496 : Vertex) (464 : Vertex) (498 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 95 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 123 = true := by
  rw [value95, value117, value118, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ∈ [(370 : Vertex), (496 : Vertex), (499 : Vertex), (506 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (498 : Vertex) [(370 : Vertex), (496 : Vertex), (499 : Vertex), (506 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 95 = true ∨ valuation q 119 = true ∨ valuation q 123 = true := by
  rw [value95, value118, value119, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(370 : Vertex), (499 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (496 : Vertex) [(370 : Vertex), (499 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 95 = true ∨ valuation q 117 = true ∨ valuation q 123 = true := by
  rw [value95, value117, value118, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(370 : Vertex), (496 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (499 : Vertex) [(370 : Vertex), (496 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 95 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value95, value117, value118, value119, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(370 : Vertex), (496 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (506 : Vertex) [(370 : Vertex), (496 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 65 = false ∨ valuation q 108 = false ∨ valuation q 118 = false := by
  rw [value65, value108, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (467 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 65 = false ∨ valuation q 108 = false ∨ valuation q 122 = false := by
  rw [value65, value108, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (467 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 65 = false ∨ valuation q 108 = false ∨ valuation q 124 = false := by
  rw [value65, value108, value119, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (467 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 65 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value65, value118, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (498 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 65 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value65, value119, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 108 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value108, value118, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (467 : Vertex) (498 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 108 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value108, value118, value119, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (467 : Vertex) (498 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 108 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value108, value119, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (467 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 118 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value118, value119, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (498 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 246 = true ∨ valuation q 65 = true ∨ valuation q 118 = true ∨ valuation q 122 = true ∨ valuation q 124 = true := by
  rw [value65, value118, value119, value122, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(243 : Vertex), (498 : Vertex), (503 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (467 : Vertex) [(243 : Vertex), (498 : Vertex), (503 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 66 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value66, value117, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (496 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 117 = true ∨ valuation q 121 = true ∨ valuation q 125 = true := by
  rw [value117, value120, value121, value125, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(496 : Vertex), (501 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (244 : Vertex) [(496 : Vertex), (501 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 66 = true ∨ valuation q 121 = true ∨ valuation q 125 = true := by
  rw [value66, value120, value121, value125, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(244 : Vertex), (501 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (496 : Vertex) [(244 : Vertex), (501 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 66 = true ∨ valuation q 117 = true ∨ valuation q 121 = true := by
  rw [value66, value117, value120, value121, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(244 : Vertex), (496 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (508 : Vertex) [(244 : Vertex), (496 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 67 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value67, value96, value109, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (245 : Vertex) (373 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 67 = false ∨ valuation q 96 = false ∨ valuation q 120 = false := by
  rw [value67, value96, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (245 : Vertex) (373 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 67 = false ∨ valuation q 96 = false ∨ valuation q 122 = false := by
  rw [value67, value96, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (245 : Vertex) (373 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 67 = false ∨ valuation q 96 = false ∨ valuation q 126 = false := by
  rw [value67, value96, value121, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (245 : Vertex) (373 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 122 = false := by
  rw [value96, value109, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (373 : Vertex) (469 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 126 = false := by
  rw [value96, value109, value121, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (373 : Vertex) (469 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E256.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112256
