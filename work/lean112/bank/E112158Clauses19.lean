import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 44 = false ∨ valuation q 95 = false ∨ valuation q 100 = false := by
  rw [value44, value95, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (403 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 95 = false ∨ valuation q 100 = false ∨ valuation q 117 = false := by
  rw [value95, value97, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (403 : Vertex) (415 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 91 = true := by
  rw [value91, value98, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(396 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 98 = true := by
  rw [value98, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(412 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (415 : Vertex) [(412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 97 = true ∨ valuation q 99 = true := by
  rw [value97, value99, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(411 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (407 : Vertex) [(411 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value96, value99, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (411 : Vertex) [(407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 50 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value50, value101, value102, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 50 = false ∨ valuation q 102 = false := by
  rw [value50, value102, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (449 : Vertex) (193 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value102, value107, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (449 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 50 = true ∨ valuation q 107 = true := by
  rw [value50, value101, value107, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(193 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (451 : Vertex) [(193 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 50 = true ∨ valuation q 102 = true := by
  rw [value50, value101, value102, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(193 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (457 : Vertex) [(193 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 52 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value52, value101, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (195 : Vertex) (449 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 52 = true ∨ valuation q 105 = true := by
  rw [value52, value102, value105, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(195 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (449 : Vertex) [(195 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 52 = true ∨ valuation q 101 = true := by
  rw [value52, value101, value102, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(195 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (455 : Vertex) [(195 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 53 = false ∨ valuation q 104 = false ∨ valuation q 111 = false := by
  rw [value53, value103, value104, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (196 : Vertex) (454 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 87 = false ∨ valuation q 104 = false ∨ valuation q 111 = false := by
  rw [value87, value103, value104, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (454 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 222 = true ∨ valuation q 103 = true ∨ valuation q 108 = true ∨ valuation q 113 = true := by
  rw [value103, value104, value108, value113, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(452 : Vertex), (462 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (455 : Vertex) [(452 : Vertex), (462 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 222 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 113 = true := by
  rw [value103, value104, value105, value113, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(452 : Vertex), (455 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (462 : Vertex) [(452 : Vertex), (455 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 222 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 108 = true := by
  rw [value103, value104, value105, value108, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(452 : Vertex), (455 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (470 : Vertex) [(452 : Vertex), (455 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 54 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value54, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 54 = false ∨ valuation q 102 = false ∨ valuation q 109 = false := by
  rw [value54, value102, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 54 = false ∨ valuation q 104 = false ∨ valuation q 109 = false := by
  rw [value54, value104, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (454 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 109 = false := by
  rw [value102, value104, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (454 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 55 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value55, value89, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (392 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 55 = false ∨ valuation q 89 = false ∨ valuation q 114 = false := by
  rw [value55, value89, value106, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (392 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 55 = false ∨ valuation q 107 = false ∨ valuation q 114 = false := by
  rw [value55, value106, value107, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (457 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 89 = false ∨ valuation q 107 = false ∨ valuation q 114 = false := by
  rw [value89, value106, value107, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (392 : Vertex) (457 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 106 = true ∨ valuation q 115 = true := by
  rw [value106, value107, value115, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(456 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (449 : Vertex) [(456 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 115 = true := by
  rw [value101, value107, value115, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(449 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (456 : Vertex) [(449 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value101, value106, value107, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(449 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (473 : Vertex) [(449 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 59 = false ∨ valuation q 104 = false ∨ valuation q 109 = false := by
  rw [value59, value104, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (454 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value104, value108, value109, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(454 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (206 : Vertex) [(454 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E158.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112158
