import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 80 = false ∨ valuation q 100 = false ∨ valuation q 104 = false := by
  rw [value80, value100, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 80 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value80, value100, value101, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 80 = false ∨ valuation q 104 = false ∨ valuation q 121 = false := by
  rw [value80, value101, value104, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 80 = false ∨ valuation q 108 = false ∨ valuation q 121 = false := by
  rw [value80, value101, value108, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 100 = false ∨ valuation q 104 = false ∨ valuation q 121 = false := by
  rw [value100, value101, value104, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 100 = false ∨ valuation q 108 = false ∨ valuation q 121 = false := by
  rw [value100, value101, value108, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 81 = false ∨ valuation q 90 = false ∨ valuation q 103 = false := by
  rw [value81, value90, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (308 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 100 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value100, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (433 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 229 = true ∨ valuation q 100 = true ∨ valuation q 102 = true ∨ valuation q 104 = true := by
  rw [value100, value102, value103, value104, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(433 : Vertex), (436 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (421 : Vertex) [(433 : Vertex), (436 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 229 = true ∨ valuation q 91 = true ∨ valuation q 102 = true ∨ valuation q 104 = true := by
  rw [value91, value102, value103, value104, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(421 : Vertex), (436 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (433 : Vertex) [(421 : Vertex), (436 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 229 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 104 = true := by
  rw [value91, value100, value103, value104, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(421 : Vertex), (433 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (436 : Vertex) [(421 : Vertex), (433 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 229 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 102 = true := by
  rw [value91, value100, value102, value103, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(421 : Vertex), (433 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (439 : Vertex) [(421 : Vertex), (433 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 93 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value93, value101, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (423 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 93 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value93, value101, value104, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (423 : Vertex) (435 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 93 = false ∨ valuation q 103 = false ∨ valuation q 109 = false := by
  rw [value93, value103, value104, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (423 : Vertex) (437 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 109 = false := by
  rw [value101, value103, value104, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (435 : Vertex) (437 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 230 = true ∨ valuation q 93 = true ∨ valuation q 101 = true ∨ valuation q 103 = true := by
  rw [value93, value101, value103, value104, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (447 : Vertex) [(423 : Vertex), (435 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 57 = false ∨ valuation q 94 = false ∨ valuation q 106 = false := by
  rw [value57, value94, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (424 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 57 = false ∨ valuation q 94 = false ∨ valuation q 107 = false := by
  rw [value57, value94, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (424 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 57 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value57, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 94 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value94, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 232 = true ∨ valuation q 105 = true ∨ valuation q 108 = true := by
  rw [value105, value106, value108, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(440 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (433 : Vertex) [(440 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 232 = true ∨ valuation q 100 = true ∨ valuation q 108 = true := by
  rw [value100, value106, value108, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(433 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (440 : Vertex) [(433 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 232 = true ∨ valuation q 100 = true ∨ valuation q 105 = true := by
  rw [value100, value105, value106, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(433 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (443 : Vertex) [(433 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 83 = false ∨ valuation q 95 = false ∨ valuation q 108 = false := by
  rw [value83, value95, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 83 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value83, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 95 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value95, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 233 = true ∨ valuation q 95 = true ∨ valuation q 105 = true ∨ valuation q 108 = true ∨ valuation q 123 = true := by
  rw [value95, value105, value107, value108, value123, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(426 : Vertex), (440 : Vertex), (443 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (314 : Vertex) [(426 : Vertex), (440 : Vertex), (443 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 233 = true ∨ valuation q 83 = true ∨ valuation q 95 = true ∨ valuation q 108 = true ∨ valuation q 123 = true := by
  rw [value83, value95, value107, value108, value123, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(314 : Vertex), (426 : Vertex), (443 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (440 : Vertex) [(314 : Vertex), (426 : Vertex), (443 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 233 = true ∨ valuation q 83 = true ∨ valuation q 95 = true ∨ valuation q 105 = true ∨ valuation q 108 = true := by
  rw [value83, value95, value105, value107, value108, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(314 : Vertex), (426 : Vertex), (440 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (506 : Vertex) [(314 : Vertex), (426 : Vertex), (440 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value96, value101, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 101 = false ∨ valuation q 107 = false := by
  rw [value96, value101, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E121.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112121
