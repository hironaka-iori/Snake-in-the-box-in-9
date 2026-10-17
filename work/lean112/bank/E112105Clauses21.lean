import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 51 = true ∨ valuation q 70 = true ∨ valuation q 104 = true ∨ valuation q 112 = true ∨ valuation q 119 = true := by
  rw [value51, value70, value104, value107, value112, value119, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(198 : Vertex), (326 : Vertex), (450 : Vertex), (462 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (390 : Vertex) [(198 : Vertex), (326 : Vertex), (450 : Vertex), (462 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 51 = true ∨ valuation q 70 = true ∨ valuation q 87 = true ∨ valuation q 104 = true ∨ valuation q 112 = true := by
  rw [value51, value70, value87, value104, value107, value112, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(198 : Vertex), (326 : Vertex), (390 : Vertex), (450 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (470 : Vertex) [(198 : Vertex), (326 : Vertex), (390 : Vertex), (450 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 73 = false ∨ valuation q 90 = false ∨ valuation q 109 = false := by
  rw [value73, value90, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (329 : Vertex) (393 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 73 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value73, value103, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (329 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 90 = false ∨ valuation q 103 = false ∨ valuation q 109 = false := by
  rw [value90, value103, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (449 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 90 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value90, value103, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 90 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value90, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 232 = true ∨ valuation q 90 = true ∨ valuation q 103 = true ∨ valuation q 109 = true ∨ valuation q 111 = true := by
  rw [value90, value103, value108, value109, value111, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(393 : Vertex), (449 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (329 : Vertex) [(393 : Vertex), (449 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 232 = true ∨ valuation q 73 = true ∨ valuation q 103 = true ∨ valuation q 109 = true ∨ valuation q 111 = true := by
  rw [value73, value103, value108, value109, value111, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(329 : Vertex), (449 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (393 : Vertex) [(329 : Vertex), (449 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 232 = true ∨ valuation q 73 = true ∨ valuation q 90 = true ∨ valuation q 109 = true ∨ valuation q 111 = true := by
  rw [value73, value90, value108, value109, value111, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(329 : Vertex), (393 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (449 : Vertex) [(329 : Vertex), (393 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 232 = true ∨ valuation q 73 = true ∨ valuation q 90 = true ∨ valuation q 103 = true ∨ valuation q 111 = true := by
  rw [value73, value90, value103, value108, value111, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(329 : Vertex), (393 : Vertex), (449 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (459 : Vertex) [(329 : Vertex), (393 : Vertex), (449 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 232 = true ∨ valuation q 73 = true ∨ valuation q 90 = true ∨ valuation q 103 = true ∨ valuation q 109 = true := by
  rw [value73, value90, value103, value108, value109, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(329 : Vertex), (393 : Vertex), (449 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (461 : Vertex) [(329 : Vertex), (393 : Vertex), (449 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 54 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value54, value105, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 54 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value54, value105, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 54 = false ∨ valuation q 108 = false ∨ valuation q 113 = false := by
  rw [value54, value108, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (203 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 113 = false := by
  rw [value105, value108, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 54 = true ∨ valuation q 108 = true ∨ valuation q 113 = true := by
  rw [value54, value108, value109, value113, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(203 : Vertex), (457 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (451 : Vertex) [(203 : Vertex), (457 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 110 = true := by
  rw [value110, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (460 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 55 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 121 = true := by
  rw [value55, value110, value111, value112, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ∈ [(204 : Vertex), (461 : Vertex), (462 : Vertex), (476 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (460 : Vertex) [(204 : Vertex), (461 : Vertex), (462 : Vertex), (476 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 55 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value55, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 55 = false ∨ valuation q 111 = false := by
  rw [value55, value111, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (460 : Vertex) (204 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 55 = false ∨ valuation q 112 = false := by
  rw [value55, value112, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (460 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value111, value112, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (460 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 112 = false ∨ valuation q 121 = false := by
  rw [value112, value121, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (460 : Vertex) (462 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 121 = true := by
  rw [value110, value111, value112, value121, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(461 : Vertex), (462 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (204 : Vertex) [(461 : Vertex), (462 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 55 = true ∨ valuation q 112 = true ∨ valuation q 121 = true := by
  rw [value55, value110, value112, value121, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(204 : Vertex), (462 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (461 : Vertex) [(204 : Vertex), (462 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 55 = true ∨ valuation q 111 = true ∨ valuation q 121 = true := by
  rw [value55, value110, value111, value121, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(204 : Vertex), (461 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (462 : Vertex) [(204 : Vertex), (461 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 55 = true ∨ valuation q 111 = true ∨ valuation q 112 = true := by
  rw [value55, value110, value111, value112, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(204 : Vertex), (461 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (476 : Vertex) [(204 : Vertex), (461 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value106, value108, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (457 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 113 = false := by
  rw [value106, value108, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 122 = false := by
  rw [value106, value108, value111, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 106 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value106, value110, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E105.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112105
