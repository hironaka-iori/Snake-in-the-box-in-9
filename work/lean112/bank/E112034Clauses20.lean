import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 91 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 111 = true := by
  rw [value91, value108, value110, value111, value112, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(423 : Vertex), (483 : Vertex), (485 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (503 : Vertex) [(423 : Vertex), (483 : Vertex), (485 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value113, value114, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (489 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 124 = false := by
  rw [value113, value114, value115, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (489 : Vertex) (490 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value113, value114, value116, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (489 : Vertex) (492 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value113, value115, value116, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (490 : Vertex) (492 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 124 = true := by
  rw [value113, value114, value115, value116, value124, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(489 : Vertex), (490 : Vertex), (492 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(489 : Vertex), (490 : Vertex), (492 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 106 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 124 = true := by
  rw [value106, value113, value115, value116, value124, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(480 : Vertex), (490 : Vertex), (492 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (489 : Vertex) [(480 : Vertex), (490 : Vertex), (492 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 106 = true ∨ valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 124 = true := by
  rw [value106, value113, value114, value116, value124, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex), (492 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (490 : Vertex) [(480 : Vertex), (489 : Vertex), (492 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 106 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 124 = true := by
  rw [value106, value113, value114, value115, value124, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex), (490 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (492 : Vertex) [(480 : Vertex), (489 : Vertex), (490 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 106 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value106, value113, value114, value115, value116, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (504 : Vertex) [(480 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 73 = false ∨ valuation q 92 = false := by
  rw [value36, value73, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (361 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 73 = false ∨ valuation q 113 = false := by
  rw [value36, value73, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (361 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 73 = false ∨ valuation q 117 = false := by
  rw [value36, value73, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (361 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 73 = false ∨ valuation q 125 = false := by
  rw [value36, value73, value114, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (361 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 92 = false ∨ valuation q 113 = false := by
  rw [value36, value92, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (425 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 92 = false ∨ valuation q 117 = false := by
  rw [value36, value92, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (425 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 92 = false ∨ valuation q 125 = false := by
  rw [value36, value92, value114, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (425 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value36, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 113 = false ∨ valuation q 125 = false := by
  rw [value36, value113, value114, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 36 = false ∨ valuation q 117 = false ∨ valuation q 125 = false := by
  rw [value36, value114, value117, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (493 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 92 = false ∨ valuation q 113 = false := by
  rw [value73, value92, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (425 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 92 = false ∨ valuation q 117 = false := by
  rw [value73, value92, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (425 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 92 = false ∨ valuation q 125 = false := by
  rw [value73, value92, value114, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (425 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value73, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 113 = false ∨ valuation q 125 = false := by
  rw [value73, value113, value114, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 117 = false ∨ valuation q 125 = false := by
  rw [value73, value114, value117, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (493 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 92 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value92, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 92 = false ∨ valuation q 113 = false ∨ valuation q 125 = false := by
  rw [value92, value113, value114, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 92 = false ∨ valuation q 117 = false ∨ valuation q 125 = false := by
  rw [value92, value114, value117, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (493 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 113 = false ∨ valuation q 117 = false ∨ valuation q 125 = false := by
  rw [value113, value114, value117, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (493 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 242 = true ∨ valuation q 36 = true ∨ valuation q 73 = true ∨ valuation q 92 = true ∨ valuation q 113 = true ∨ valuation q 117 = true := by
  rw [value36, value73, value92, value113, value114, value117, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (489 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(233 : Vertex), (361 : Vertex), (425 : Vertex), (488 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (489 : Vertex) (505 : Vertex) [(233 : Vertex), (361 : Vertex), (425 : Vertex), (488 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 37 = false ∨ valuation q 74 = false ∨ valuation q 93 = false := by
  rw [value37, value74, value93, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E034.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112034
