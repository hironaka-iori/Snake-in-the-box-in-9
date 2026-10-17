import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 116 = false := by
  rw [value110, value111, value112, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (482 : Vertex) (484 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value110, value111, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (482 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value110, value112, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (484 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 54 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value54, value110, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (354 : Vertex) (480 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 233 = true ∨ valuation q 83 = true ∨ valuation q 110 = true ∨ valuation q 114 = true := by
  rw [value83, value110, value111, value114, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(418 : Vertex), (480 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (354 : Vertex) [(418 : Vertex), (480 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 233 = true ∨ valuation q 54 = true ∨ valuation q 83 = true ∨ valuation q 110 = true := by
  rw [value54, value83, value110, value111, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(354 : Vertex), (418 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (490 : Vertex) [(354 : Vertex), (418 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 234 = true ∨ valuation q 103 = true ∨ valuation q 110 = true ∨ valuation q 115 = true ∨ valuation q 118 = true := by
  rw [value103, value110, value112, value115, value118, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(452 : Vertex), (480 : Vertex), (492 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (356 : Vertex) [(452 : Vertex), (480 : Vertex), (492 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 234 = true ∨ valuation q 56 = true ∨ valuation q 103 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value56, value103, value110, value112, value118, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(356 : Vertex), (452 : Vertex), (480 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (492 : Vertex) [(356 : Vertex), (452 : Vertex), (480 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 235 = true ∨ valuation q 87 = true ∨ valuation q 110 = true ∨ valuation q 114 = true ∨ valuation q 115 = true := by
  rw [value87, value110, value113, value114, value115, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex), (490 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (360 : Vertex) [(424 : Vertex), (480 : Vertex), (490 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 235 = true ∨ valuation q 57 = true ∨ valuation q 87 = true ∨ valuation q 110 = true ∨ valuation q 115 = true := by
  rw [value57, value87, value110, value113, value115, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(360 : Vertex), (424 : Vertex), (480 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (490 : Vertex) [(360 : Vertex), (424 : Vertex), (480 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 58 = false ∨ valuation q 111 = false ∨ valuation q 120 = false := by
  rw [value58, value111, value114, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (482 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 58 = false ∨ valuation q 113 = false ∨ valuation q 120 = false := by
  rw [value58, value113, value114, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 120 = false := by
  rw [value111, value113, value114, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (482 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 90 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value90, value112, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (428 : Vertex) (484 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 238 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 118 = true := by
  rw [value110, value116, value117, value118, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(480 : Vertex), (497 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (368 : Vertex) [(480 : Vertex), (497 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 238 = true ∨ valuation q 59 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value59, value110, value116, value118, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(368 : Vertex), (480 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (497 : Vertex) [(368 : Vertex), (480 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 238 = true ∨ valuation q 59 = true ∨ valuation q 110 = true ∨ valuation q 117 = true := by
  rw [value59, value110, value116, value117, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(368 : Vertex), (480 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (500 : Vertex) [(368 : Vertex), (480 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 93 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value93, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (496 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 239 = true ∨ valuation q 93 = true ∨ valuation q 116 = true := by
  rw [value93, value116, value117, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(433 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (505 : Vertex) [(433 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 105 = false ∨ valuation q 112 = false ∨ valuation q 116 = false := by
  rw [value105, value112, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (468 : Vertex) (484 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 240 = true ∨ valuation q 112 = true ∨ valuation q 116 = true := by
  rw [value112, value116, value118, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(484 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (468 : Vertex) [(484 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 241 = true ∨ valuation q 117 = true ∨ valuation q 121 = true := by
  rw [value117, value119, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(497 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (377 : Vertex) [(497 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 241 = true ∨ valuation q 60 = true ∨ valuation q 121 = true := by
  rw [value60, value119, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(377 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (497 : Vertex) [(377 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 241 = true ∨ valuation q 60 = true ∨ valuation q 117 = true := by
  rw [value60, value117, value119, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(377 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (509 : Vertex) [(377 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 242 = true ∨ valuation q 122 = true := by
  rw [value120, value122, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(510 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (490 : Vertex) [(510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 242 = true ∨ valuation q 114 = true := by
  rw [value114, value120, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(490 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (510 : Vertex) [(490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 243 = true := by
  rw [value121, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (509 : Vertex) (505 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 63 = false ∨ valuation q 108 = false ∨ valuation q 120 = false := by
  rw [value63, value108, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (510 : Vertex) (382 : Vertex) (478 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 244 = true ∨ valuation q 108 = true ∨ valuation q 120 = true := by
  rw [value108, value120, value122, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (510 : Vertex) w → w ∈ region → w ≠ (382 : Vertex) → w ∈ [(478 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (510 : Vertex) (382 : Vertex) [(478 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 244 = true ∨ valuation q 63 = true ∨ valuation q 108 = true := by
  rw [value63, value108, value122, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (510 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(382 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (510 : Vertex) (506 : Vertex) [(382 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 124 = false := by
  rw [value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (69 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (103 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block19 (q : Snake 81) (h : Conditions q) : B112E258.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112258
