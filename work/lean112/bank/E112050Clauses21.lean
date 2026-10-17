import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 128 = false := by
  rw [value101, value104, value107, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 108 = false ∨ valuation q 128 = false := by
  rw [value101, value107, value108, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 104 = false ∨ valuation q 108 = false ∨ valuation q 128 = false := by
  rw [value104, value107, value108, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (410 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 31 = false ∨ valuation q 67 = false ∨ valuation q 105 = false := by
  rw [value31, value67, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (287 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 31 = false ∨ valuation q 67 = false ∨ valuation q 106 = false := by
  rw [value31, value67, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (287 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 31 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value31, value102, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 31 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value31, value102, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 31 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value31, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value67, value102, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value67, value102, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value67, value102, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 67 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value67, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 67 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value67, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (411 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 67 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value67, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value102, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value102, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (411 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value102, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 67 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 107 = true := by
  rw [value67, value102, value105, value106, value107, value108, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(287 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (159 : Vertex) [(287 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 31 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 107 = true := by
  rw [value31, value102, value105, value106, value107, value108, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(159 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (287 : Vertex) [(159 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 31 = true ∨ valuation q 67 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 107 = true := by
  rw [value31, value67, value105, value106, value107, value108, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(159 : Vertex), (287 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (407 : Vertex) [(159 : Vertex), (287 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 31 = true ∨ valuation q 67 = true ∨ valuation q 102 = true ∨ valuation q 106 = true ∨ valuation q 107 = true := by
  rw [value31, value67, value102, value106, value107, value108, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(159 : Vertex), (287 : Vertex), (407 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (411 : Vertex) [(159 : Vertex), (287 : Vertex), (407 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 86 = false ∨ valuation q 110 = false ∨ valuation q 120 = false := by
  rw [value86, value109, value110, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 86 = true ∨ valuation q 110 = true ∨ valuation q 112 = true ∨ valuation q 120 = true := by
  rw [value86, value109, value110, value112, value120, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(384 : Vertex), (449 : Vertex), (452 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (192 : Vertex) [(384 : Vertex), (449 : Vertex), (452 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 32 = true ∨ valuation q 86 = true ∨ valuation q 110 = true ∨ valuation q 120 = true := by
  rw [value32, value86, value109, value110, value120, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(192 : Vertex), (384 : Vertex), (449 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (452 : Vertex) [(192 : Vertex), (384 : Vertex), (449 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 32 = true ∨ valuation q 86 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value32, value86, value109, value110, value112, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(192 : Vertex), (384 : Vertex), (449 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (464 : Vertex) [(192 : Vertex), (384 : Vertex), (449 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value109, value110, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value109, value110, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value109, value110, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value110, value111, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 238 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 113 = true := by
  rw [value109, value110, value111, value113, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(448 : Vertex), (451 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (457 : Vertex) [(448 : Vertex), (451 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 110 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value110, value111, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (455 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 110 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value110, value111, value114, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E050.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112050
