import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 237 = true ∨ valuation q 92 = true ∨ valuation q 116 = true ∨ valuation q 119 = true := by
  rw [value92, value114, value116, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(433 : Vertex), (501 : Vertex), (505 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (481 : Vertex) [(433 : Vertex), (501 : Vertex), (505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 237 = true ∨ valuation q 92 = true ∨ valuation q 102 = true ∨ valuation q 119 = true := by
  rw [value92, value102, value114, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(433 : Vertex), (481 : Vertex), (505 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (501 : Vertex) [(433 : Vertex), (481 : Vertex), (505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 237 = true ∨ valuation q 92 = true ∨ valuation q 102 = true ∨ valuation q 116 = true := by
  rw [value92, value102, value114, value116, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(433 : Vertex), (481 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (505 : Vertex) [(433 : Vertex), (481 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 77 = false ∨ valuation q 104 = false ∨ valuation q 117 = false := by
  rw [value77, value104, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (484 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 238 = true ∨ valuation q 77 = true ∨ valuation q 104 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value77, value104, value115, value116, value117, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(372 : Vertex), (484 : Vertex), (501 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (244 : Vertex) [(372 : Vertex), (484 : Vertex), (501 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 238 = true ∨ valuation q 41 = true ∨ valuation q 77 = true ∨ valuation q 104 = true ∨ valuation q 116 = true := by
  rw [value41, value77, value104, value115, value116, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(244 : Vertex), (372 : Vertex), (484 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (502 : Vertex) [(244 : Vertex), (372 : Vertex), (484 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value105, value114, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (485 : Vertex) (497 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value105, value114, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (485 : Vertex) (497 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value105, value114, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (485 : Vertex) (497 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value105, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (485 : Vertex) (500 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 122 = false := by
  rw [value105, value115, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (485 : Vertex) (500 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value105, value116, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (485 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value114, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (497 : Vertex) (500 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 122 = false := by
  rw [value114, value115, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (497 : Vertex) (500 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 114 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value114, value116, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (497 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 115 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value115, value116, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (500 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 95 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value95, value106, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (438 : Vertex) (486 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 95 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value95, value106, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (438 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 95 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value95, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (438 : Vertex) (500 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 106 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value106, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (486 : Vertex) (500 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value116, value117, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (501 : Vertex) (502 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 241 = true ∨ valuation q 117 = true ∨ valuation q 123 = true := by
  rw [value117, value118, value123, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(502 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (501 : Vertex) [(502 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 241 = true ∨ valuation q 116 = true ∨ valuation q 123 = true := by
  rw [value116, value118, value123, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(501 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (502 : Vertex) [(501 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 241 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value116, value117, value118, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(501 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (511 : Vertex) [(501 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 108 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value108, value114, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 108 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value108, value114, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (497 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 108 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value108, value119, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 114 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value114, value119, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (497 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 242 = true ∨ valuation q 108 = true ∨ valuation q 121 = true ∨ valuation q 122 = true := by
  rw [value108, value119, value121, value122, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(489 : Vertex), (507 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (497 : Vertex) [(489 : Vertex), (507 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 242 = true ∨ valuation q 108 = true ∨ valuation q 114 = true ∨ valuation q 122 = true := by
  rw [value108, value114, value119, value122, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(489 : Vertex), (497 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (507 : Vertex) [(489 : Vertex), (497 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 243 = true ∨ valuation q 109 = true ∨ valuation q 121 = true := by
  rw [value109, value120, value121, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(490 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (250 : Vertex) [(490 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 244 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 123 = true := by
  rw [value119, value120, value121, value123, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(505 : Vertex), (506 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (491 : Vertex) [(505 : Vertex), (506 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E097.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112097
