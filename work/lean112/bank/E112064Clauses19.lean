import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 227 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 115 = true := by
  rw [value109, value110, value111, value112, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (209 : Vertex) [(464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 227 = true ∨ valuation q 38 = true ∨ valuation q 109 = true ∨ valuation q 112 = true ∨ valuation q 115 = true := by
  rw [value38, value109, value110, value112, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(209 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (467 : Vertex) [(209 : Vertex), (464 : Vertex), (469 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 227 = true ∨ valuation q 38 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value38, value109, value110, value111, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(209 : Vertex), (464 : Vertex), (467 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (469 : Vertex) [(209 : Vertex), (464 : Vertex), (467 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 76 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value76, value110, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (339 : Vertex) (465 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 103 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value103, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (465 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 229 = true ∨ valuation q 110 = true ∨ valuation q 113 = true := by
  rw [value110, value112, value113, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(465 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (453 : Vertex) [(465 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 79 = false ∨ valuation q 112 = false ∨ valuation q 117 = false := by
  rw [value79, value112, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (343 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 230 = true ∨ valuation q 79 = true ∨ valuation q 112 = true ∨ valuation q 117 = true := by
  rw [value79, value112, value113, value117, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(343 : Vertex), (469 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (467 : Vertex) [(343 : Vertex), (469 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 230 = true ∨ valuation q 79 = true ∨ valuation q 111 = true ∨ valuation q 117 = true := by
  rw [value79, value111, value113, value117, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(343 : Vertex), (467 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (469 : Vertex) [(343 : Vertex), (467 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 230 = true ∨ valuation q 79 = true ∨ valuation q 111 = true ∨ valuation q 112 = true := by
  rw [value79, value111, value112, value113, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(343 : Vertex), (467 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (479 : Vertex) [(343 : Vertex), (467 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 42 = false ∨ valuation q 109 = false ∨ valuation q 115 = false := by
  rw [value42, value109, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (216 : Vertex) (464 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 231 = true ∨ valuation q 80 = true ∨ valuation q 109 = true ∨ valuation q 115 = true := by
  rw [value80, value109, value114, value115, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(344 : Vertex), (464 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (216 : Vertex) [(344 : Vertex), (464 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 231 = true ∨ valuation q 42 = true ∨ valuation q 109 = true ∨ valuation q 115 = true := by
  rw [value42, value109, value114, value115, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(216 : Vertex), (464 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (344 : Vertex) [(216 : Vertex), (464 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 231 = true ∨ valuation q 42 = true ∨ valuation q 80 = true ∨ valuation q 115 = true := by
  rw [value42, value80, value114, value115, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(216 : Vertex), (344 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(216 : Vertex), (344 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 231 = true ∨ valuation q 42 = true ∨ valuation q 80 = true ∨ valuation q 109 = true := by
  rw [value42, value80, value109, value114, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(216 : Vertex), (344 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (473 : Vertex) [(216 : Vertex), (344 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 81 = false ∨ valuation q 105 = false ∨ valuation q 110 = false := by
  rw [value81, value105, value110, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (345 : Vertex) (457 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 81 = false ∨ valuation q 105 = false ∨ valuation q 114 = false := by
  rw [value81, value105, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (345 : Vertex) (457 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 81 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value81, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (345 : Vertex) (465 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 105 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value105, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (457 : Vertex) (465 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 232 = true ∨ valuation q 81 = true ∨ valuation q 110 = true ∨ valuation q 114 = true := by
  rw [value81, value110, value114, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(345 : Vertex), (465 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (473 : Vertex) (457 : Vertex) [(345 : Vertex), (465 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 232 = true ∨ valuation q 81 = true ∨ valuation q 105 = true ∨ valuation q 110 = true := by
  rw [value81, value105, value110, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(345 : Vertex), (457 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (473 : Vertex) (472 : Vertex) [(345 : Vertex), (457 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 85 = false ∨ valuation q 108 = false ∨ valuation q 117 = false := by
  rw [value85, value108, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (350 : Vertex) (462 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 233 = true ∨ valuation q 85 = true ∨ valuation q 108 = true ∨ valuation q 117 = true := by
  rw [value85, value108, value116, value117, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(350 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (222 : Vertex) [(350 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 233 = true ∨ valuation q 45 = true ∨ valuation q 108 = true ∨ valuation q 117 = true := by
  rw [value45, value108, value116, value117, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(222 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (350 : Vertex) [(222 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 233 = true ∨ valuation q 45 = true ∨ valuation q 85 = true ∨ valuation q 117 = true := by
  rw [value45, value85, value116, value117, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(222 : Vertex), (350 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (462 : Vertex) [(222 : Vertex), (350 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 233 = true ∨ valuation q 45 = true ∨ valuation q 85 = true ∨ valuation q 108 = true := by
  rw [value45, value85, value108, value116, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(222 : Vertex), (350 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (479 : Vertex) [(222 : Vertex), (350 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 46 = false ∨ valuation q 86 = false ∨ valuation q 113 = false := by
  rw [value46, value86, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (223 : Vertex) (351 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 46 = false ∨ valuation q 86 = false ∨ valuation q 116 = false := by
  rw [value46, value86, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (223 : Vertex) (351 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value46, value113, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (223 : Vertex) (471 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 86 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value86, value113, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (351 : Vertex) (471 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 234 = true ∨ valuation q 86 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value86, value113, value116, value117, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (479 : Vertex) w → w ∈ region → w ≠ (223 : Vertex) → w ∈ [(351 : Vertex), (471 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (479 : Vertex) (223 : Vertex) [(351 : Vertex), (471 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 234 = true ∨ valuation q 46 = true ∨ valuation q 86 = true ∨ valuation q 113 = true := by
  rw [value46, value86, value113, value117, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (479 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(223 : Vertex), (351 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (479 : Vertex) (478 : Vertex) [(223 : Vertex), (351 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E064.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112064
