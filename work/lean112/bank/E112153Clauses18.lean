import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 92 = true ∨ valuation q 102 = true ∨ valuation q 116 = true := by
  rw [value92, value102, value115, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(400 : Vertex), (448 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (472 : Vertex) [(400 : Vertex), (448 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value105, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value105, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 123 = false := by
  rw [value105, value115, value116, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value105, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (469 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value105, value116, value117, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (469 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 118 = false ∨ valuation q 123 = false := by
  rw [value105, value116, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (470 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 115 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value115, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (464 : Vertex) (469 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 115 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value115, value116, value117, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (464 : Vertex) (469 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 115 = false ∨ valuation q 118 = false ∨ valuation q 123 = false := by
  rw [value115, value116, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (464 : Vertex) (470 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 123 = false := by
  rw [value116, value117, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (469 : Vertex) (470 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 41 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value41, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 77 = true ∨ valuation q 106 = true ∨ valuation q 116 = true ∨ valuation q 119 = true := by
  rw [value77, value106, value116, value117, value119, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(341 : Vertex), (453 : Vertex), (468 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (213 : Vertex) [(341 : Vertex), (453 : Vertex), (468 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 116 = false ∨ valuation q 119 = false ∨ valuation q 124 = false := by
  rw [value116, value118, value119, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (468 : Vertex) (471 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 119 = true ∨ valuation q 124 = true := by
  rw [value118, value119, value124, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (470 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(471 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (470 : Vertex) (468 : Vertex) [(471 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 116 = true ∨ valuation q 124 = true := by
  rw [value116, value118, value124, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (470 : Vertex) w → w ∈ region → w ≠ (471 : Vertex) → w ∈ [(468 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (470 : Vertex) (471 : Vertex) [(468 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 116 = true ∨ valuation q 119 = true := by
  rw [value116, value118, value119, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (470 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(468 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (470 : Vertex) (478 : Vertex) [(468 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 96 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value96, value107, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (407 : Vertex) (455 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 96 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value96, value107, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (407 : Vertex) (455 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 96 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value96, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (407 : Vertex) (469 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 107 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value107, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (455 : Vertex) (469 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 108 = true ∨ valuation q 115 = true ∨ valuation q 121 = true ∨ valuation q 123 = true := by
  rw [value108, value115, value120, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ∈ [(456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (472 : Vertex) [(456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 108 = false ∨ valuation q 115 = false ∨ valuation q 121 = false := by
  rw [value108, value115, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (456 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 108 = false ∨ valuation q 115 = false ∨ valuation q 123 = false := by
  rw [value108, value115, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (456 : Vertex) (464 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 108 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value108, value120, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (456 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 115 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value115, value120, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (464 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 108 = true ∨ valuation q 121 = true ∨ valuation q 123 = true := by
  rw [value108, value120, value121, value123, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(456 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(456 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 120 = false ∨ valuation q 124 = false := by
  rw [value110, value120, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (458 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value110, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (458 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 120 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value120, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (472 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 120 = true ∨ valuation q 122 = true ∨ valuation q 124 = true := by
  rw [value120, value121, value122, value124, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(472 : Vertex), (475 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (458 : Vertex) [(472 : Vertex), (475 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 110 = true ∨ valuation q 120 = true ∨ valuation q 124 = true := by
  rw [value110, value120, value121, value124, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(458 : Vertex), (472 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (475 : Vertex) [(458 : Vertex), (472 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E153.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112153
