import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 87 = false ∨ valuation q 102 = false ∨ valuation q 118 = false := by
  rw [value87, value102, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (451 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 87 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value87, value106, value110, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 102 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value102, value106, value110, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 227 = true ∨ valuation q 46 = true ∨ valuation q 87 = true ∨ valuation q 102 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value46, value87, value102, value106, value110, value118, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(203 : Vertex), (395 : Vertex), (451 : Vertex), (463 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (331 : Vertex) [(203 : Vertex), (395 : Vertex), (451 : Vertex), (463 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 227 = true ∨ valuation q 46 = true ∨ valuation q 67 = true ∨ valuation q 102 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value46, value67, value102, value106, value110, value118, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (395 : Vertex) → w ∈ [(203 : Vertex), (331 : Vertex), (451 : Vertex), (463 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (395 : Vertex) [(203 : Vertex), (331 : Vertex), (451 : Vertex), (463 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 47 = false ∨ valuation q 68 = false ∨ valuation q 88 = false := by
  rw [value47, value68, value88, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (332 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 47 = false ∨ valuation q 68 = false ∨ valuation q 109 = false := by
  rw [value47, value68, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (332 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 47 = false ∨ valuation q 68 = false ∨ valuation q 119 = false := by
  rw [value47, value68, value107, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (332 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 47 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value47, value105, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (456 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 47 = false ∨ valuation q 105 = false ∨ valuation q 119 = false := by
  rw [value47, value105, value107, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (456 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 47 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value47, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 47 = false ∨ valuation q 108 = false ∨ valuation q 119 = false := by
  rw [value47, value107, value108, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (461 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 68 = false ∨ valuation q 88 = false ∨ valuation q 109 = false := by
  rw [value68, value88, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (332 : Vertex) (396 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 68 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value68, value105, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (332 : Vertex) (456 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 68 = false ∨ valuation q 108 = false ∨ valuation q 119 = false := by
  rw [value68, value107, value108, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (332 : Vertex) (461 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 68 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value68, value107, value109, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (332 : Vertex) (462 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 88 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value88, value105, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (396 : Vertex) (456 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value105, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (456 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value105, value107, value109, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (456 : Vertex) (462 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value107, value108, value109, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (461 : Vertex) (462 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value103, value107, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 229 = true ∨ valuation q 107 = true ∨ valuation q 110 = true := by
  rw [value107, value108, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(460 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (453 : Vertex) [(460 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 229 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value103, value107, value108, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(453 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (463 : Vertex) [(453 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 69 = false ∨ valuation q 89 = false := by
  rw [value48, value69, value89, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 69 = false ∨ valuation q 107 = false := by
  rw [value48, value69, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 69 = false ∨ valuation q 110 = false := by
  rw [value48, value69, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 69 = false ∨ valuation q 120 = false := by
  rw [value48, value69, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value48, value89, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value48, value89, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 89 = false ∨ valuation q 120 = false := by
  rw [value48, value89, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value48, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 48 = false ∨ valuation q 107 = false ∨ valuation q 120 = false := by
  rw [value48, value107, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E019.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112019
