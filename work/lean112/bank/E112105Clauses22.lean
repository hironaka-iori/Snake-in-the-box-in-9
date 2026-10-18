import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 106 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value106, value110, value111, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (460 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 106 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value106, value111, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value108, value110, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (457 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value108, value110, value111, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (457 : Vertex) (460 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 108 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value108, value111, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (457 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value110, value111, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (460 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 113 = true ∨ valuation q 122 = true := by
  rw [value108, value110, value111, value113, value122, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(457 : Vertex), (460 : Vertex), (463 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (453 : Vertex) [(457 : Vertex), (460 : Vertex), (463 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 106 = true ∨ valuation q 110 = true ∨ valuation q 113 = true ∨ valuation q 122 = true := by
  rw [value106, value110, value111, value113, value122, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(453 : Vertex), (460 : Vertex), (463 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (457 : Vertex) [(453 : Vertex), (460 : Vertex), (463 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 113 = true ∨ valuation q 122 = true := by
  rw [value106, value108, value111, value113, value122, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(453 : Vertex), (457 : Vertex), (463 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (460 : Vertex) [(453 : Vertex), (457 : Vertex), (463 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 122 = true := by
  rw [value106, value108, value110, value111, value122, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(453 : Vertex), (457 : Vertex), (460 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (463 : Vertex) [(453 : Vertex), (457 : Vertex), (460 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 113 = true := by
  rw [value106, value108, value110, value111, value113, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(453 : Vertex), (457 : Vertex), (460 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (477 : Vertex) [(453 : Vertex), (457 : Vertex), (460 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 74 = false ∨ valuation q 91 = false := by
  rw [value56, value74, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 74 = false ∨ valuation q 107 = false := by
  rw [value56, value74, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 74 = false ∨ valuation q 110 = false := by
  rw [value56, value74, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 74 = false ∨ valuation q 113 = false := by
  rw [value56, value74, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 74 = false ∨ valuation q 123 = false := by
  rw [value56, value74, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 91 = false ∨ valuation q 107 = false := by
  rw [value56, value91, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 91 = false ∨ valuation q 110 = false := by
  rw [value56, value91, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value56, value91, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 91 = false ∨ valuation q 123 = false := by
  rw [value56, value91, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value56, value107, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (454 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value56, value107, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (454 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 107 = false ∨ valuation q 123 = false := by
  rw [value56, value107, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (454 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value56, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 110 = false ∨ valuation q 123 = false := by
  rw [value56, value110, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 56 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value56, value112, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 91 = false ∨ valuation q 107 = false := by
  rw [value74, value91, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 91 = false ∨ valuation q 110 = false := by
  rw [value74, value91, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value74, value91, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 91 = false ∨ valuation q 123 = false := by
  rw [value74, value91, value112, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value74, value107, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (454 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 74 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value74, value107, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (454 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E105.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112105
