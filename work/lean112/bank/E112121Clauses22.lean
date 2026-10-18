import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 48 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value48, value94, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 73 = false ∨ valuation q 95 = false ∨ valuation q 114 = false := by
  rw [value73, value94, value95, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 73 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value73, value94, value97, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 73 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value73, value94, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 105 = false := by
  rw [value87, value94, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value87, value94, value97, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value94, value95, value97, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (426 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value94, value95, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (426 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 105 = false ∨ valuation q 114 = false := by
  rw [value94, value95, value105, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (426 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 105 = false ∨ valuation q 114 = false := by
  rw [value94, value97, value105, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (428 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 89 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value89, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (424 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 89 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value89, value94, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (424 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 89 = false ∨ valuation q 94 = false ∨ valuation q 107 = false := by
  rw [value89, value94, value95, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (424 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 89 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value89, value95, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 89 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value89, value95, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value89, value95, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value94, value95, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (424 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value94, value95, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (424 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value94, value95, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (424 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value95, value96, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (427 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 49 = false ∨ valuation q 75 = false ∨ valuation q 108 = false := by
  rw [value49, value75, value96, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (299 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 49 = false ∨ valuation q 95 = false ∨ valuation q 108 = false := by
  rw [value49, value95, value96, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 222 = true ∨ valuation q 75 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 108 = true ∨ valuation q 116 = true := by
  rw [value75, value95, value96, value99, value108, value116, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(299 : Vertex), (426 : Vertex), (431 : Vertex), (443 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (171 : Vertex) [(299 : Vertex), (426 : Vertex), (431 : Vertex), (443 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 222 = true ∨ valuation q 49 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 108 = true ∨ valuation q 116 = true := by
  rw [value49, value95, value96, value99, value108, value116, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(171 : Vertex), (426 : Vertex), (431 : Vertex), (443 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (299 : Vertex) [(171 : Vertex), (426 : Vertex), (431 : Vertex), (443 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 222 = true ∨ valuation q 49 = true ∨ valuation q 75 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 108 = true := by
  rw [value49, value75, value95, value96, value99, value108, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(171 : Vertex), (299 : Vertex), (426 : Vertex), (431 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (491 : Vertex) [(171 : Vertex), (299 : Vertex), (426 : Vertex), (431 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value90, value94, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (420 : Vertex) (424 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 223 = true ∨ valuation q 94 = true ∨ valuation q 98 = true := by
  rw [value94, value97, value98, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(424 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(424 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value90, value94, value97, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(420 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value92, value95, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 224 = true ∨ valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 99 = true := by
  rw [value95, value97, value98, value99, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(426 : Vertex), (428 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (422 : Vertex) [(426 : Vertex), (428 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 224 = true ∨ valuation q 92 = true ∨ valuation q 97 = true ∨ valuation q 99 = true := by
  rw [value92, value97, value98, value99, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(422 : Vertex), (428 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (426 : Vertex) [(422 : Vertex), (428 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 224 = true ∨ valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 99 = true := by
  rw [value92, value95, value98, value99, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(422 : Vertex), (426 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (428 : Vertex) [(422 : Vertex), (426 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block22 (q : Snake 81) (h : Conditions q) : B112E121.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112121
