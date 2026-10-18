import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 99 = false ∨ valuation q 127 = false := by
  rw [value43, value99, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (435 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value43, value108, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (483 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 108 = false ∨ valuation q 127 = false := by
  rw [value43, value108, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (483 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value43, value119, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (497 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value43, value119, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 43 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value43, value120, value123, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 119 = false := by
  rw [value80, value99, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 123 = false := by
  rw [value80, value99, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (435 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 127 = false := by
  rw [value80, value99, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (435 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 80 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value80, value108, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (483 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 80 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value80, value119, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 80 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value80, value120, value123, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 99 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value99, value108, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (483 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 99 = false ∨ valuation q 108 = false ∨ valuation q 127 = false := by
  rw [value99, value108, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (483 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 99 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value99, value119, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (497 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 99 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value99, value119, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 99 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value99, value120, value123, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 108 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value108, value119, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (483 : Vertex) (497 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 108 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value108, value119, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (483 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 108 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value108, value120, value123, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (483 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 119 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value119, value120, value123, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (497 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value110, value119, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (485 : Vertex) (497 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 123 = false ∨ valuation q 128 = false := by
  rw [value110, value121, value123, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (485 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 119 = true ∨ valuation q 123 = true ∨ valuation q 128 = true := by
  rw [value119, value121, value123, value128, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(497 : Vertex), (503 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (485 : Vertex) [(497 : Vertex), (503 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 110 = true ∨ valuation q 123 = true ∨ valuation q 128 = true := by
  rw [value110, value121, value123, value128, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(485 : Vertex), (503 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (497 : Vertex) [(485 : Vertex), (503 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 110 = true ∨ valuation q 119 = true ∨ valuation q 128 = true := by
  rw [value110, value119, value121, value128, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(485 : Vertex), (497 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (503 : Vertex) [(485 : Vertex), (497 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 110 = true ∨ valuation q 119 = true ∨ valuation q 123 = true := by
  rw [value110, value119, value121, value123, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(485 : Vertex), (497 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (509 : Vertex) [(485 : Vertex), (497 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 45 = false ∨ valuation q 111 = false ∨ valuation q 123 = false := by
  rw [value45, value111, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (246 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 111 = true ∨ valuation q 123 = true := by
  rw [value111, value122, value123, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(486 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (246 : Vertex) [(486 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 45 = true ∨ valuation q 123 = true := by
  rw [value45, value122, value123, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(246 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (486 : Vertex) [(246 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 45 = true ∨ valuation q 111 = true := by
  rw [value45, value111, value122, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(246 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (503 : Vertex) [(246 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 112 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value112, value120, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (499 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E034.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112034
