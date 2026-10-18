import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value86, value98, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (433 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 99 = false ∨ valuation q 103 = false := by
  rw [value86, value98, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (433 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value86, value98, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (434 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value86, value98, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (434 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value86, value98, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value98, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (433 : Vertex) (434 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value98, value99, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (433 : Vertex) (434 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value98, value99, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (433 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 100 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value98, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (434 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 86 = true ∨ valuation q 100 = true ∨ valuation q 102 = true ∨ valuation q 103 = true := by
  rw [value86, value98, value100, value102, value103, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(416 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (433 : Vertex) [(416 : Vertex), (434 : Vertex), (436 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 223 = true ∨ valuation q 98 = true ∨ valuation q 101 = true := by
  rw [value98, value99, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(432 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (417 : Vertex) [(432 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 223 = true ∨ valuation q 87 = true ∨ valuation q 101 = true := by
  rw [value87, value99, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(417 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (432 : Vertex) [(417 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 223 = true ∨ valuation q 87 = true ∨ valuation q 98 = true := by
  rw [value87, value98, value99, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(417 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (435 : Vertex) [(417 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 43 = false ∨ valuation q 78 = false ∨ valuation q 88 = false := by
  rw [value43, value78, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (306 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 43 = false ∨ valuation q 78 = false ∨ valuation q 101 = false := by
  rw [value43, value78, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (306 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 43 = false ∨ valuation q 78 = false ∨ valuation q 117 = false := by
  rw [value43, value78, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (306 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 43 = false ∨ valuation q 88 = false ∨ valuation q 117 = false := by
  rw [value43, value88, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (418 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 43 = false ∨ valuation q 98 = false ∨ valuation q 117 = false := by
  rw [value43, value98, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (432 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 43 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value43, value100, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 43 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value43, value100, value101, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (435 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 117 = false := by
  rw [value78, value88, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (306 : Vertex) (418 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 98 = false ∨ valuation q 117 = false := by
  rw [value78, value98, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (306 : Vertex) (432 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value78, value100, value101, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (306 : Vertex) (435 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 117 = false := by
  rw [value88, value98, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (418 : Vertex) (432 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value88, value100, value101, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (418 : Vertex) (435 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value98, value100, value101, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (432 : Vertex) (435 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 224 = true ∨ valuation q 43 = true ∨ valuation q 78 = true ∨ valuation q 88 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 104 = true := by
  rw [value43, value78, value88, value98, value100, value101, value104, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(178 : Vertex), (306 : Vertex), (418 : Vertex), (432 : Vertex), (435 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (498 : Vertex) [(178 : Vertex), (306 : Vertex), (418 : Vertex), (432 : Vertex), (435 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value89, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 105 = false := by
  rw [value89, value99, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 105 = false := by
  rw [value89, value100, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (434 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 105 = false := by
  rw [value99, value100, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (434 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value89, value99, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E008.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112008
