import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 80 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value80, value105, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (324 : Vertex) (468 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 114 = false := by
  rw [value102, value105, value106, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (448 : Vertex) (453 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 102 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value102, value105, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (448 : Vertex) (468 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value105, value107, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (454 : Vertex) (468 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 81 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value81, value103, value106, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 81 = false ∨ valuation q 103 = false ∨ valuation q 115 = false := by
  rw [value81, value103, value106, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (449 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 81 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value81, value106, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (461 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 81 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value81, value106, value115, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (469 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 111 = false := by
  rw [value103, value105, value106, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (449 : Vertex) (452 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 115 = false := by
  rw [value103, value105, value106, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (449 : Vertex) (452 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 103 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value103, value106, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (449 : Vertex) (461 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 103 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value103, value106, value111, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (449 : Vertex) (461 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 103 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value103, value106, value115, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (449 : Vertex) (469 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 105 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value105, value106, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (452 : Vertex) (461 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 105 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value105, value106, value111, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (452 : Vertex) (461 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value105, value106, value115, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (452 : Vertex) (469 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 111 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value106, value111, value115, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (461 : Vertex) (469 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 234 = true ∨ valuation q 82 = true := by
  rw [value82, value107, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (452 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 84 = false ∨ valuation q 102 = false ∨ valuation q 121 = false := by
  rw [value84, value102, value108, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (448 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 102 = true ∨ valuation q 109 = true ∨ valuation q 121 = true := by
  rw [value102, value108, value109, value121, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(448 : Vertex), (457 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (328 : Vertex) [(448 : Vertex), (457 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 103 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value103, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (449 : Vertex) (456 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 103 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value103, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (449 : Vertex) (456 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 103 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value103, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (449 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value108, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (456 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 104 = false ∨ valuation q 109 = false ∨ valuation q 123 = false := by
  rw [value104, value109, value110, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 237 = true ∨ valuation q 104 = true ∨ valuation q 109 = true ∨ valuation q 123 = true := by
  rw [value104, value109, value110, value123, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(451 : Vertex), (457 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (203 : Vertex) [(451 : Vertex), (457 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 237 = true ∨ valuation q 43 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value43, value104, value109, value110, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(203 : Vertex), (451 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (491 : Vertex) [(203 : Vertex), (451 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 238 = true ∨ valuation q 87 = true ∨ valuation q 106 = true ∨ valuation q 109 = true ∨ valuation q 125 = true := by
  rw [value87, value106, value109, value111, value125, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(333 : Vertex), (453 : Vertex), (457 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (205 : Vertex) [(333 : Vertex), (453 : Vertex), (457 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 238 = true ∨ valuation q 45 = true ∨ valuation q 106 = true ∨ valuation q 109 = true ∨ valuation q 125 = true := by
  rw [value45, value106, value109, value111, value125, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(205 : Vertex), (453 : Vertex), (457 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (333 : Vertex) [(205 : Vertex), (453 : Vertex), (457 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 238 = true ∨ valuation q 45 = true ∨ valuation q 87 = true ∨ valuation q 106 = true ∨ valuation q 125 = true := by
  rw [value45, value87, value106, value111, value125, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(205 : Vertex), (333 : Vertex), (453 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (457 : Vertex) [(205 : Vertex), (333 : Vertex), (453 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 238 = true ∨ valuation q 45 = true ∨ valuation q 87 = true ∨ valuation q 106 = true ∨ valuation q 109 = true := by
  rw [value45, value87, value106, value109, value111, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(205 : Vertex), (333 : Vertex), (453 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (493 : Vertex) [(205 : Vertex), (333 : Vertex), (453 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 49 = false ∨ valuation q 90 = false ∨ valuation q 113 = false := by
  rw [value49, value90, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (338 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E260.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112260
