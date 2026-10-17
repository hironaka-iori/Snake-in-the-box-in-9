import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 110 = false ∨ valuation q 116 = false ∨ valuation q 122 = false := by
  rw [value110, value111, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 122 = false := by
  rw [value111, value114, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (455 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 122 = true := by
  rw [value111, value114, value116, value122, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (449 : Vertex) [(455 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 110 = true ∨ valuation q 114 = true ∨ valuation q 122 = true := by
  rw [value110, value111, value114, value122, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(449 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 110 = true ∨ valuation q 114 = true ∨ valuation q 116 = true := by
  rw [value110, value111, value114, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (467 : Vertex) [(449 : Vertex), (455 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 69 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value69, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (324 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value88, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 70 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value70, value89, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (389 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 70 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value70, value110, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (449 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 70 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value70, value110, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 70 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value70, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (455 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 89 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value89, value110, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 89 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value89, value110, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 89 = true ∨ valuation q 110 = true ∨ valuation q 112 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value89, value110, value112, value113, value114, value117, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(389 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (325 : Vertex) [(389 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 70 = true ∨ valuation q 110 = true ∨ valuation q 112 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value70, value110, value112, value113, value114, value117, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(325 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (389 : Vertex) [(325 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 70 = true ∨ valuation q 89 = true ∨ valuation q 110 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value70, value89, value110, value113, value114, value117, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(325 : Vertex), (389 : Vertex), (449 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (452 : Vertex) [(325 : Vertex), (389 : Vertex), (449 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 70 = true ∨ valuation q 89 = true ∨ valuation q 110 = true ∨ valuation q 112 = true ∨ valuation q 114 = true := by
  rw [value70, value89, value110, value112, value113, value114, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(325 : Vertex), (389 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (461 : Vertex) [(325 : Vertex), (389 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 72 = false ∨ valuation q 91 = false := by
  rw [value35, value72, value91, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 72 = false ∨ valuation q 111 = false := by
  rw [value35, value72, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 72 = false ∨ valuation q 113 = false := by
  rw [value35, value72, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 72 = false ∨ valuation q 119 = false := by
  rw [value35, value72, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 72 = false ∨ valuation q 123 = false := by
  rw [value35, value72, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 91 = false ∨ valuation q 111 = false := by
  rw [value35, value91, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value35, value91, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 91 = false ∨ valuation q 119 = false := by
  rw [value35, value91, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 91 = false ∨ valuation q 123 = false := by
  rw [value35, value91, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value35, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value35, value111, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 111 = false ∨ valuation q 123 = false := by
  rw [value35, value111, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value35, value113, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value35, value113, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (453 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 35 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value35, value114, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E050.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112050
