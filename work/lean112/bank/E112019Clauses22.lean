import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 110 = false ∨ valuation q 120 = false := by
  rw [value48, value109, value110, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 69 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value69, value89, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 69 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value69, value89, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 69 = false ∨ valuation q 89 = false ∨ valuation q 120 = false := by
  rw [value69, value89, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 69 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value69, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 69 = false ∨ valuation q 107 = false ∨ valuation q 120 = false := by
  rw [value69, value107, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 69 = false ∨ valuation q 110 = false ∨ valuation q 120 = false := by
  rw [value69, value109, value110, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 89 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value89, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 89 = false ∨ valuation q 107 = false ∨ valuation q 120 = false := by
  rw [value89, value107, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 89 = false ∨ valuation q 110 = false ∨ valuation q 120 = false := by
  rw [value89, value109, value110, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 107 = false ∨ valuation q 110 = false ∨ valuation q 120 = false := by
  rw [value107, value109, value110, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (460 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 230 = true ∨ valuation q 69 = true ∨ valuation q 89 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 120 = true := by
  rw [value69, value89, value107, value109, value110, value120, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(334 : Vertex), (398 : Vertex), (460 : Vertex), (463 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (206 : Vertex) [(334 : Vertex), (398 : Vertex), (460 : Vertex), (463 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 230 = true ∨ valuation q 48 = true ∨ valuation q 69 = true ∨ valuation q 89 = true ∨ valuation q 110 = true ∨ valuation q 120 = true := by
  rw [value48, value69, value89, value109, value110, value120, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(206 : Vertex), (334 : Vertex), (398 : Vertex), (463 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (460 : Vertex) [(206 : Vertex), (334 : Vertex), (398 : Vertex), (463 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 230 = true ∨ valuation q 48 = true ∨ valuation q 69 = true ∨ valuation q 89 = true ∨ valuation q 107 = true ∨ valuation q 120 = true := by
  rw [value48, value69, value89, value107, value109, value120, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(206 : Vertex), (334 : Vertex), (398 : Vertex), (460 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (463 : Vertex) [(206 : Vertex), (334 : Vertex), (398 : Vertex), (460 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 230 = true ∨ valuation q 48 = true ∨ valuation q 69 = true ∨ valuation q 89 = true ∨ valuation q 107 = true ∨ valuation q 110 = true := by
  rw [value48, value69, value89, value107, value109, value110, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(206 : Vertex), (334 : Vertex), (398 : Vertex), (460 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (478 : Vertex) [(206 : Vertex), (334 : Vertex), (398 : Vertex), (460 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 121 = true := by
  rw [value104, value106, value108, value109, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (463 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value104, value106, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (459 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 121 = false := by
  rw [value104, value106, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (459 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 104 = false ∨ valuation q 109 = false ∨ valuation q 121 = false := by
  rw [value104, value109, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (462 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value106, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 121 = false := by
  rw [value106, value108, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 121 = false := by
  rw [value106, value109, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (462 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 121 = false := by
  rw [value108, value109, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (461 : Vertex) (462 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 231 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 121 = true := by
  rw [value106, value108, value109, value110, value121, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(459 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (455 : Vertex) [(459 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 231 = true ∨ valuation q 104 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 121 = true := by
  rw [value104, value108, value109, value110, value121, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(455 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (459 : Vertex) [(455 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 231 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 109 = true ∨ valuation q 121 = true := by
  rw [value104, value106, value109, value110, value121, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (461 : Vertex) [(455 : Vertex), (459 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 231 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 121 = true := by
  rw [value104, value106, value108, value110, value121, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (462 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 231 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 109 = true := by
  rw [value104, value106, value108, value109, value110, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (479 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value99, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (465 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 112 = false ∨ valuation q 115 = false := by
  rw [value99, value111, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (465 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 112 = false ∨ valuation q 116 = false := by
  rw [value99, value111, value112, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (465 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value99, value111, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E019.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112019
