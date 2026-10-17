import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 237 = true ∨ valuation q 113 = true ∨ valuation q 115 = true ∨ valuation q 121 = true := by
  rw [value110, value113, value115, value121, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (449 : Vertex) [(455 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 237 = true ∨ valuation q 109 = true ∨ valuation q 115 = true ∨ valuation q 121 = true := by
  rw [value109, value110, value115, value121, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(449 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (455 : Vertex) [(449 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 237 = true ∨ valuation q 109 = true ∨ valuation q 113 = true ∨ valuation q 121 = true := by
  rw [value109, value110, value113, value121, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(449 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 237 = true ∨ valuation q 109 = true ∨ valuation q 113 = true ∨ valuation q 115 = true := by
  rw [value109, value110, value113, value115, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (467 : Vertex) [(449 : Vertex), (455 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 68 = false ∨ valuation q 87 = false ∨ valuation q 108 = false := by
  rw [value68, value87, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (324 : Vertex) (388 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 68 = false ∨ valuation q 87 = false ∨ valuation q 112 = false := by
  rw [value68, value87, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (324 : Vertex) (388 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 68 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value68, value108, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (324 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 87 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value87, value108, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 238 = true ∨ valuation q 68 = true ∨ valuation q 87 = true ∨ valuation q 108 = true := by
  rw [value68, value87, value108, value111, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(324 : Vertex), (388 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (453 : Vertex) [(324 : Vertex), (388 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 69 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value69, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (449 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 69 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value69, value109, value112, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 69 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value69, value112, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (455 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value88, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value88, value109, value112, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value88, value112, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (455 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value111, value112, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (452 : Vertex) (455 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 88 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value88, value109, value111, value112, value113, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(389 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (325 : Vertex) [(389 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 69 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value69, value109, value111, value112, value113, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(325 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (389 : Vertex) [(325 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 69 = true ∨ valuation q 88 = true ∨ valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value69, value88, value111, value112, value113, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(325 : Vertex), (389 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (449 : Vertex) [(325 : Vertex), (389 : Vertex), (452 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 69 = true ∨ valuation q 88 = true ∨ valuation q 109 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value69, value88, value109, value112, value113, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(325 : Vertex), (389 : Vertex), (449 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (452 : Vertex) [(325 : Vertex), (389 : Vertex), (449 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 69 = true ∨ valuation q 88 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 116 = true := by
  rw [value69, value88, value109, value111, value112, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(325 : Vertex), (389 : Vertex), (449 : Vertex), (452 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (455 : Vertex) [(325 : Vertex), (389 : Vertex), (449 : Vertex), (452 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 69 = true ∨ valuation q 88 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 113 = true := by
  rw [value69, value88, value109, value111, value112, value113, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(325 : Vertex), (389 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (461 : Vertex) [(325 : Vertex), (389 : Vertex), (449 : Vertex), (452 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 71 = false ∨ valuation q 90 = false := by
  rw [value35, value71, value90, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 71 = false ∨ valuation q 110 = false := by
  rw [value35, value71, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 71 = false ∨ valuation q 112 = false := by
  rw [value35, value71, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 71 = false ∨ valuation q 118 = false := by
  rw [value35, value71, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 71 = false ∨ valuation q 122 = false := by
  rw [value35, value71, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value35, value90, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value35, value90, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 90 = false ∨ valuation q 118 = false := by
  rw [value35, value90, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 90 = false ∨ valuation q 122 = false := by
  rw [value35, value90, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value35, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E052.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112052
