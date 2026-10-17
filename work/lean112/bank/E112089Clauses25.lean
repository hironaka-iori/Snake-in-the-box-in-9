import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 79 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value79, value91, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 79 = false ∨ valuation q 91 = false ∨ valuation q 102 = false := by
  rw [value79, value91, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 79 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value79, value92, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 79 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value79, value92, value94, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 79 = false ∨ valuation q 96 = false ∨ valuation q 102 = false := by
  rw [value79, value92, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (395 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value91, value92, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value91, value92, value94, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 96 = false ∨ valuation q 102 = false := by
  rw [value91, value92, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (395 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 102 = false := by
  rw [value92, value94, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (391 : Vertex) (395 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 216 = true ∨ valuation q 79 = true ∨ valuation q 91 = true ∨ valuation q 96 = true ∨ valuation q 102 = true := by
  rw [value79, value91, value92, value96, value102, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (387 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(259 : Vertex), (386 : Vertex), (395 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (387 : Vertex) (391 : Vertex) [(259 : Vertex), (386 : Vertex), (395 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 217 = true ∨ valuation q 98 = true := by
  rw [value93, value98, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(397 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (391 : Vertex) [(397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 217 = true ∨ valuation q 94 = true := by
  rw [value93, value94, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(391 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (397 : Vertex) [(391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 94 = true := by
  rw [value94, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (391 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ∈ [(387 : Vertex), (389 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (391 : Vertex) [(387 : Vertex), (389 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value92, value93, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (391 : Vertex) (387 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 218 = true ∨ valuation q 93 = true := by
  rw [value93, value94, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(389 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (387 : Vertex) [(389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 218 = true ∨ valuation q 92 = true := by
  rw [value92, value94, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(387 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (389 : Vertex) [(387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 42 = false ∨ valuation q 81 = false ∨ valuation q 91 = false := by
  rw [value42, value81, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 42 = false ∨ valuation q 81 = false ∨ valuation q 96 = false := by
  rw [value42, value81, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 42 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value42, value91, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 81 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value81, value91, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 81 = true ∨ valuation q 91 = true ∨ valuation q 96 = true := by
  rw [value81, value91, value95, value96, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(266 : Vertex), (386 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (138 : Vertex) [(266 : Vertex), (386 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 42 = true ∨ valuation q 91 = true ∨ valuation q 96 = true := by
  rw [value42, value91, value95, value96, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(138 : Vertex), (386 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (266 : Vertex) [(138 : Vertex), (386 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 42 = true ∨ valuation q 81 = true ∨ valuation q 91 = true := by
  rw [value42, value81, value91, value95, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (395 : Vertex) → w ∈ [(138 : Vertex), (266 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (395 : Vertex) [(138 : Vertex), (266 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 43 = true ∨ valuation q 92 = true ∨ valuation q 95 = true := by
  rw [value43, value92, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ∈ [(139 : Vertex), (387 : Vertex), (394 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (395 : Vertex) [(139 : Vertex), (387 : Vertex), (394 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 43 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value43, value92, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (387 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value92, value95, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (395 : Vertex) (387 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide)

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 220 = true ∨ valuation q 92 = true ∨ valuation q 95 = true := by
  rw [value92, value95, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(387 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (139 : Vertex) [(387 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 220 = true ∨ valuation q 43 = true ∨ valuation q 95 = true := by
  rw [value43, value95, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(139 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (387 : Vertex) [(139 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 220 = true ∨ valuation q 43 = true ∨ valuation q 92 = true := by
  rw [value43, value92, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(139 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (394 : Vertex) [(139 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 44 = false ∨ valuation q 98 = false ∨ valuation q 104 = false := by
  rw [value44, value97, value98, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (140 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 44 = true ∨ valuation q 104 = true := by
  rw [value44, value97, value104, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(140 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (397 : Vertex) [(140 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block25 (q : Snake 81) (h : Conditions q) : B112E089.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112089
