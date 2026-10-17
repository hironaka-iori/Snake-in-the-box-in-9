import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 46 = true ∨ valuation q 107 = true ∨ valuation q 119 = true := by
  rw [value46, value107, value108, value119, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(211 : Vertex), (465 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (475 : Vertex) [(211 : Vertex), (465 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 46 = true ∨ valuation q 107 = true ∨ valuation q 112 = true := by
  rw [value46, value107, value108, value112, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(211 : Vertex), (465 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (499 : Vertex) [(211 : Vertex), (465 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 236 = true ∨ valuation q 85 = true ∨ valuation q 107 = true ∨ valuation q 114 = true ∨ valuation q 121 = true := by
  rw [value85, value107, value109, value114, value121, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(341 : Vertex), (465 : Vertex), (477 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (213 : Vertex) [(341 : Vertex), (465 : Vertex), (477 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 236 = true ∨ valuation q 48 = true ∨ valuation q 85 = true ∨ valuation q 114 = true ∨ valuation q 121 = true := by
  rw [value48, value85, value109, value114, value121, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(213 : Vertex), (341 : Vertex), (477 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (465 : Vertex) [(213 : Vertex), (341 : Vertex), (477 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 236 = true ∨ valuation q 48 = true ∨ valuation q 85 = true ∨ valuation q 107 = true ∨ valuation q 114 = true := by
  rw [value48, value85, value107, value109, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(213 : Vertex), (341 : Vertex), (465 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (501 : Vertex) [(213 : Vertex), (341 : Vertex), (465 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 106 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value106, value110, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (464 : Vertex) (473 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 50 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value50, value107, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (217 : Vertex) (465 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 238 = true ∨ valuation q 87 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 112 = true ∨ valuation q 114 = true := by
  rw [value87, value107, value110, value111, value112, value114, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(345 : Vertex), (465 : Vertex), (472 : Vertex), (475 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (473 : Vertex) (217 : Vertex) [(345 : Vertex), (465 : Vertex), (472 : Vertex), (475 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 103 = false ∨ valuation q 108 = false := by
  rw [value88, value103, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value88, value103, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (459 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 103 = false ∨ valuation q 124 = false := by
  rw [value88, value103, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (459 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value88, value108, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (467 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 108 = false ∨ valuation q 124 = false := by
  rw [value88, value108, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (467 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value88, value111, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (473 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 103 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value103, value108, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (459 : Vertex) (467 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 103 = false ∨ valuation q 108 = false ∨ valuation q 124 = false := by
  rw [value103, value108, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (459 : Vertex) (467 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 103 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value103, value111, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (459 : Vertex) (473 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 108 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value108, value111, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (467 : Vertex) (473 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 104 = false ∨ valuation q 110 = false ∨ valuation q 125 = false := by
  rw [value104, value110, value113, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (460 : Vertex) (472 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 53 = false ∨ valuation q 90 = false ∨ valuation q 105 = false := by
  rw [value53, value90, value105, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (349 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 53 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value53, value105, value109, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (461 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 90 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value90, value105, value109, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (349 : Vertex) (461 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 90 = false ∨ valuation q 105 = false ∨ valuation q 111 = false := by
  rw [value90, value105, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (349 : Vertex) (461 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 90 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value90, value105, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (349 : Vertex) (461 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 90 = false ∨ valuation q 111 = false ∨ valuation q 126 = false := by
  rw [value90, value111, value114, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (349 : Vertex) (473 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value105, value109, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (461 : Vertex) (469 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value105, value109, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (461 : Vertex) (469 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 126 = false := by
  rw [value105, value109, value114, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (461 : Vertex) (469 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 105 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value105, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (461 : Vertex) (473 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 105 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value105, value113, value114, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (461 : Vertex) (476 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value109, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (469 : Vertex) (473 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value109, value113, value114, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (469 : Vertex) (476 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E256.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112256
