import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 80 = false ∨ valuation q 105 = false := by
  rw [value44, value80, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 80 = false ∨ valuation q 109 = false := by
  rw [value44, value80, value102, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 80 = false ∨ valuation q 122 = false := by
  rw [value44, value80, value102, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value44, value101, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value44, value101, value102, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value44, value101, value102, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value44, value102, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 105 = false ∨ valuation q 122 = false := by
  rw [value44, value102, value105, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 44 = false ∨ valuation q 109 = false ∨ valuation q 122 = false := by
  rw [value44, value102, value109, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 80 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value80, value101, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 80 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value80, value101, value102, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 80 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value80, value101, value102, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 80 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value80, value102, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 80 = false ∨ valuation q 105 = false ∨ valuation q 122 = false := by
  rw [value80, value102, value105, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 80 = false ∨ valuation q 109 = false ∨ valuation q 122 = false := by
  rw [value80, value102, value109, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value101, value102, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 122 = false := by
  rw [value101, value102, value105, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 101 = false ∨ valuation q 109 = false ∨ valuation q 122 = false := by
  rw [value101, value102, value109, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 122 = false := by
  rw [value102, value105, value109, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 91 = false ∨ valuation q 104 = false ∨ valuation q 123 = false := by
  rw [value91, value103, value104, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (420 : Vertex) (437 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 91 = true ∨ valuation q 104 = true ∨ valuation q 123 = true := by
  rw [value91, value103, value104, value123, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(420 : Vertex), (437 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (308 : Vertex) [(420 : Vertex), (437 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 81 = true ∨ valuation q 104 = true ∨ valuation q 123 = true := by
  rw [value81, value103, value104, value123, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(308 : Vertex), (437 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (420 : Vertex) [(308 : Vertex), (437 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 81 = true ∨ valuation q 91 = true ∨ valuation q 123 = true := by
  rw [value81, value91, value103, value123, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(308 : Vertex), (420 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (437 : Vertex) [(308 : Vertex), (420 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 81 = true ∨ valuation q 91 = true ∨ valuation q 104 = true := by
  rw [value81, value91, value103, value104, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(308 : Vertex), (420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (500 : Vertex) [(308 : Vertex), (420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 92 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value92, value101, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (433 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 92 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value92, value101, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 92 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value92, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value101, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (433 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 92 = false ∨ valuation q 105 = false := by
  rw [value92, value105, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (437 : Vertex) (421 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 232 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 105 = true := by
  rw [value101, value103, value104, value105, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(433 : Vertex), (436 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (421 : Vertex) [(433 : Vertex), (436 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 232 = true ∨ valuation q 92 = true ∨ valuation q 101 = true ∨ valuation q 103 = true := by
  rw [value92, value101, value103, value104, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(421 : Vertex), (433 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (439 : Vertex) [(421 : Vertex), (433 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 233 = true ∨ valuation q 102 = true ∨ valuation q 104 = true ∨ valuation q 110 = true := by
  rw [value102, value104, value105, value110, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(435 : Vertex), (437 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (423 : Vertex) [(435 : Vertex), (437 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E036.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112036
