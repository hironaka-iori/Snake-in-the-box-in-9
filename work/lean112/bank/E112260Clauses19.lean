import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 112 = true := by
  rw [value90, value112, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(466 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (342 : Vertex) [(466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 92 = true := by
  rw [value90, value92, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(342 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (466 : Vertex) [(342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 81 = false ∨ valuation q 89 = false ∨ valuation q 100 = false := by
  rw [value81, value89, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (337 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 81 = false ∨ valuation q 89 = false ∨ valuation q 115 = false := by
  rw [value81, value89, value91, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (337 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 115 = false := by
  rw [value81, value91, value100, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (373 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 115 = false := by
  rw [value89, value91, value100, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (337 : Vertex) (373 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 81 = true ∨ valuation q 100 = true ∨ valuation q 115 = true := by
  rw [value81, value91, value100, value115, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(325 : Vertex), (373 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (337 : Vertex) [(325 : Vertex), (373 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 81 = true ∨ valuation q 89 = true ∨ valuation q 115 = true := by
  rw [value81, value89, value91, value115, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(325 : Vertex), (337 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (373 : Vertex) [(325 : Vertex), (337 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 81 = true ∨ valuation q 89 = true ∨ valuation q 100 = true := by
  rw [value81, value89, value91, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(325 : Vertex), (337 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (469 : Vertex) [(325 : Vertex), (337 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 219 = true ∨ valuation q 90 = true := by
  rw [value90, value92, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (326 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 219 = true ∨ valuation q 82 = true := by
  rw [value82, value92, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (338 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 79 = false ∨ valuation q 96 = false ∨ valuation q 117 = false := by
  rw [value79, value93, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (323 : Vertex) (359 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 220 = true ∨ valuation q 96 = true ∨ valuation q 117 = true := by
  rw [value93, value96, value117, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(359 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (323 : Vertex) [(359 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 220 = true ∨ valuation q 79 = true ∨ valuation q 117 = true := by
  rw [value79, value93, value117, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(323 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (359 : Vertex) [(323 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 20 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value20, value76, value81, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (293 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 20 = false ∨ valuation q 76 = false ∨ valuation q 96 = false := by
  rw [value20, value76, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (293 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 20 = false ∨ valuation q 81 = false ∨ valuation q 96 = false := by
  rw [value20, value81, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (325 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 20 = false ∨ valuation q 81 = false ∨ valuation q 98 = false := by
  rw [value20, value81, value94, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (325 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 20 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value20, value81, value94, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (325 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 20 = false ∨ valuation q 81 = false ∨ valuation q 119 = false := by
  rw [value20, value81, value94, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (325 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 96 = false := by
  rw [value76, value81, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (325 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value76, value81, value94, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (325 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 76 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value76, value94, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (359 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 76 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value76, value94, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (359 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 76 = false ∨ valuation q 96 = false ∨ valuation q 119 = false := by
  rw [value76, value94, value96, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (359 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 76 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value76, value94, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (365 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 76 = false ∨ valuation q 98 = false ∨ valuation q 119 = false := by
  rw [value76, value94, value98, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (365 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 76 = false ∨ valuation q 100 = false ∨ valuation q 119 = false := by
  rw [value76, value94, value100, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (373 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 81 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value81, value94, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (325 : Vertex) (359 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 81 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value81, value94, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (325 : Vertex) (359 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 81 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value81, value94, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (325 : Vertex) (365 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 119 = false := by
  rw [value81, value94, value100, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (325 : Vertex) (373 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E260.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112260
