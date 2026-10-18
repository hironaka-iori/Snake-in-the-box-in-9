import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 51 = false ∨ valuation q 76 = false ∨ valuation q 120 = false := by
  rw [value51, value74, value76, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 62 = false ∨ valuation q 69 = false ∨ valuation q 75 = false := by
  rw [value62, value69, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 62 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value62, value69, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 62 = false ∨ valuation q 69 = false ∨ valuation q 120 = false := by
  rw [value62, value69, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (208 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 62 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value62, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 62 = false ∨ valuation q 75 = false ∨ valuation q 120 = false := by
  rw [value62, value74, value75, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 62 = false ∨ valuation q 76 = false ∨ valuation q 120 = false := by
  rw [value62, value74, value76, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value69, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 120 = false := by
  rw [value69, value74, value75, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 69 = false ∨ valuation q 76 = false ∨ valuation q 120 = false := by
  rw [value69, value74, value76, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 120 = false := by
  rw [value74, value75, value76, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (218 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 120 = true := by
  rw [value51, value62, value69, value74, value75, value76, value120, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(152 : Vertex), (200 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (88 : Vertex) [(152 : Vertex), (200 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 32 = true ∨ valuation q 62 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 120 = true := by
  rw [value32, value62, value69, value74, value75, value76, value120, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(88 : Vertex), (200 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (152 : Vertex) [(88 : Vertex), (200 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 32 = true ∨ valuation q 51 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 120 = true := by
  rw [value32, value51, value69, value74, value75, value76, value120, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(88 : Vertex), (152 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (200 : Vertex) [(88 : Vertex), (152 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 32 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 120 = true := by
  rw [value32, value51, value62, value74, value75, value76, value120, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(88 : Vertex), (152 : Vertex), (200 : Vertex), (218 : Vertex), (220 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (208 : Vertex) [(88 : Vertex), (152 : Vertex), (200 : Vertex), (218 : Vertex), (220 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 32 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 69 = true ∨ valuation q 76 = true ∨ valuation q 120 = true := by
  rw [value32, value51, value62, value69, value74, value76, value120, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(88 : Vertex), (152 : Vertex), (200 : Vertex), (208 : Vertex), (220 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (218 : Vertex) [(88 : Vertex), (152 : Vertex), (200 : Vertex), (208 : Vertex), (220 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 32 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 120 = true := by
  rw [value32, value51, value62, value69, value74, value75, value120, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(88 : Vertex), (152 : Vertex), (200 : Vertex), (208 : Vertex), (218 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (220 : Vertex) [(88 : Vertex), (152 : Vertex), (200 : Vertex), (208 : Vertex), (218 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 32 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value32, value51, value62, value69, value74, value75, value76, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(88 : Vertex), (152 : Vertex), (200 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (472 : Vertex) [(88 : Vertex), (152 : Vertex), (200 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 75 = true := by
  rw [value75, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (218 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 71 = false := by
  rw [value33, value53, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 74 = false := by
  rw [value33, value53, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 78 = false := by
  rw [value33, value53, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 121 = false := by
  rw [value33, value53, value75, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value33, value71, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value33, value71, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (210 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 121 = false := by
  rw [value33, value71, value75, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (210 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value33, value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (216 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 74 = false ∨ valuation q 121 = false := by
  rw [value33, value74, value75, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (216 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 78 = false ∨ valuation q 121 = false := by
  rw [value33, value75, value78, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (222 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 53 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value53, value71, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 53 = false ∨ valuation q 71 = false ∨ valuation q 121 = false := by
  rw [value53, value71, value75, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 53 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value53, value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (216 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E089.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112089
