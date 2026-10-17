import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 56 = false ∨ valuation q 112 = false ∨ valuation q 117 = false := by
  rw [value56, value112, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (481 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 56 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value56, value112, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 56 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value56, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 56 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value56, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 56 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value56, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 112 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value112, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 112 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value112, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 112 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value112, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 115 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value115, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value112, value118, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (489 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 244 = true ∨ valuation q 56 = true ∨ valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 118 = true := by
  rw [value56, value115, value116, value117, value118, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (489 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(233 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (489 : Vertex) (481 : Vertex) [(233 : Vertex), (488 : Vertex), (491 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 58 = false ∨ valuation q 97 = false ∨ valuation q 116 = false := by
  rw [value58, value97, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (427 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 58 = false ∨ valuation q 97 = false ∨ valuation q 119 = false := by
  rw [value58, value97, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (427 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 58 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value58, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (489 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 97 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value97, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (489 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 245 = true ∨ valuation q 97 = true ∨ valuation q 116 = true ∨ valuation q 119 = true := by
  rw [value97, value116, value117, value119, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(427 : Vertex), (489 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (235 : Vertex) [(427 : Vertex), (489 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 245 = true ∨ valuation q 58 = true ∨ valuation q 116 = true ∨ valuation q 119 = true := by
  rw [value58, value116, value117, value119, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(235 : Vertex), (489 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (427 : Vertex) [(235 : Vertex), (489 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 245 = true ∨ valuation q 58 = true ∨ valuation q 97 = true ∨ valuation q 119 = true := by
  rw [value58, value97, value117, value119, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(235 : Vertex), (427 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (489 : Vertex) [(235 : Vertex), (427 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 245 = true ∨ valuation q 58 = true ∨ valuation q 97 = true ∨ valuation q 116 = true := by
  rw [value58, value97, value116, value117, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(235 : Vertex), (427 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (495 : Vertex) [(235 : Vertex), (427 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 116 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value116, value118, value119, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (489 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 246 = true ∨ valuation q 116 = true ∨ valuation q 127 = true := by
  rw [value116, value118, value127, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(489 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (495 : Vertex) [(489 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 246 = true ∨ valuation q 116 = true ∨ valuation q 119 = true := by
  rw [value116, value118, value119, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(489 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (509 : Vertex) [(489 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 100 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value100, value114, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 100 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value100, value114, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (487 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 100 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value100, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 114 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value114, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (487 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 247 = true ∨ valuation q 100 = true ∨ valuation q 117 = true ∨ valuation q 118 = true := by
  rw [value100, value117, value118, value119, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(431 : Vertex), (491 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (487 : Vertex) [(431 : Vertex), (491 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 247 = true ∨ valuation q 100 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value100, value114, value117, value119, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(431 : Vertex), (487 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (493 : Vertex) [(431 : Vertex), (487 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 101 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value101, value112, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value101, value122, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (497 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value112, value122, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (497 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 248 = true ∨ valuation q 101 = true ∨ valuation q 122 = true := by
  rw [value101, value120, value122, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(433 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (481 : Vertex) [(433 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block22 (q : Snake 81) (h : Conditions q) : B112E036.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112036
