import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 112 = false ∨ valuation q 120 = false ∨ valuation q 122 = false := by
  rw [value112, value120, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 112 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value112, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (501 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value120, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (499 : Vertex) (501 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 251 = true ∨ valuation q 112 = true ∨ valuation q 120 = true ∨ valuation q 122 = true := by
  rw [value112, value120, value122, value123, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(487 : Vertex), (499 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (501 : Vertex) [(487 : Vertex), (499 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 82 = false ∨ valuation q 113 = false := by
  rw [value46, value82, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (376 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 125 = false := by
  rw [value46, value113, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value46, value113, value124, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 125 = false ∨ valuation q 126 = false := by
  rw [value46, value124, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (505 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 113 = false ∨ valuation q 125 = false := by
  rw [value82, value113, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (376 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 113 = false ∨ valuation q 126 = false := by
  rw [value82, value113, value124, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (376 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 125 = false ∨ valuation q 126 = false := by
  rw [value82, value124, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (376 : Vertex) (505 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 113 = false ∨ valuation q 125 = false ∨ valuation q 126 = false := by
  rw [value113, value124, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (488 : Vertex) (505 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 252 = true ∨ valuation q 82 = true ∨ valuation q 113 = true ∨ valuation q 125 = true ∨ valuation q 126 = true := by
  rw [value82, value113, value124, value125, value126, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (504 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(376 : Vertex), (488 : Vertex), (505 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (504 : Vertex) (248 : Vertex) [(376 : Vertex), (488 : Vertex), (505 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 114 = false ∨ valuation q 119 = false ∨ valuation q 124 = false := by
  rw [value114, value119, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (497 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 114 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value114, value119, value125, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 114 = false ∨ valuation q 119 = false ∨ valuation q 128 = false := by
  rw [value114, value119, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (497 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 114 = false ∨ valuation q 124 = false ∨ valuation q 128 = false := by
  rw [value114, value124, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (504 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 114 = false ∨ valuation q 127 = false ∨ valuation q 128 = false := by
  rw [value114, value125, value127, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 119 = false ∨ valuation q 124 = false ∨ valuation q 128 = false := by
  rw [value119, value124, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (497 : Vertex) (504 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 119 = false ∨ valuation q 127 = false ∨ valuation q 128 = false := by
  rw [value119, value125, value127, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (497 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 119 = true ∨ valuation q 124 = true ∨ valuation q 127 = true ∨ valuation q 128 = true := by
  rw [value119, value124, value125, value127, value128, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(497 : Vertex), (504 : Vertex), (507 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (489 : Vertex) [(497 : Vertex), (504 : Vertex), (507 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 114 = true ∨ valuation q 124 = true ∨ valuation q 127 = true ∨ valuation q 128 = true := by
  rw [value114, value124, value125, value127, value128, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(489 : Vertex), (504 : Vertex), (507 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (497 : Vertex) [(489 : Vertex), (504 : Vertex), (507 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 114 = true ∨ valuation q 119 = true ∨ valuation q 127 = true ∨ valuation q 128 = true := by
  rw [value114, value119, value125, value127, value128, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(489 : Vertex), (497 : Vertex), (507 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (504 : Vertex) [(489 : Vertex), (497 : Vertex), (507 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 114 = true ∨ valuation q 119 = true ∨ valuation q 124 = true ∨ valuation q 128 = true := by
  rw [value114, value119, value124, value125, value128, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(489 : Vertex), (497 : Vertex), (504 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (507 : Vertex) [(489 : Vertex), (497 : Vertex), (504 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 114 = true ∨ valuation q 119 = true ∨ valuation q 124 = true ∨ valuation q 127 = true := by
  rw [value114, value119, value124, value125, value127, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(489 : Vertex), (497 : Vertex), (504 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (509 : Vertex) [(489 : Vertex), (497 : Vertex), (504 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 101 = false ∨ valuation q 115 = false ∨ valuation q 124 = false := by
  rw [value101, value115, value124, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (442 : Vertex) (490 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 101 = false ∨ valuation q 115 = false ∨ valuation q 127 = false := by
  rw [value101, value115, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (442 : Vertex) (490 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 101 = false ∨ valuation q 124 = false ∨ valuation q 127 = false := by
  rw [value101, value124, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (442 : Vertex) (504 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 115 = false ∨ valuation q 124 = false ∨ valuation q 127 = false := by
  rw [value115, value124, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (490 : Vertex) (504 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 254 = true ∨ valuation q 115 = true ∨ valuation q 124 = true ∨ valuation q 127 = true := by
  rw [value115, value124, value126, value127, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(490 : Vertex), (504 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (442 : Vertex) [(490 : Vertex), (504 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 254 = true ∨ valuation q 101 = true ∨ valuation q 124 = true ∨ valuation q 127 = true := by
  rw [value101, value124, value126, value127, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(442 : Vertex), (504 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (490 : Vertex) [(442 : Vertex), (504 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 254 = true ∨ valuation q 101 = true ∨ valuation q 115 = true ∨ valuation q 127 = true := by
  rw [value101, value115, value126, value127, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(442 : Vertex), (490 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (504 : Vertex) [(442 : Vertex), (490 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block25 (q : Snake 81) (h : Conditions q) : B112E034.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112034
