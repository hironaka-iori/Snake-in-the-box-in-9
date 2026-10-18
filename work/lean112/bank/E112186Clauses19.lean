import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 106 = false ∨ valuation q 111 = false ∨ valuation q 121 = false := by
  rw [value106, value111, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (450 : Vertex) (456 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 106 = false ∨ valuation q 115 = false ∨ valuation q 121 = false := by
  rw [value106, value113, value115, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (450 : Vertex) (462 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 111 = false ∨ valuation q 115 = false ∨ valuation q 121 = false := by
  rw [value111, value113, value115, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (456 : Vertex) (462 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 106 = true ∨ valuation q 111 = true ∨ valuation q 115 = true ∨ valuation q 121 = true := by
  rw [value106, value111, value113, value115, value121, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(450 : Vertex), (456 : Vertex), (462 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (394 : Vertex) [(450 : Vertex), (456 : Vertex), (462 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 89 = true ∨ valuation q 106 = true ∨ valuation q 111 = true ∨ valuation q 121 = true := by
  rw [value89, value106, value111, value113, value121, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(394 : Vertex), (450 : Vertex), (456 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (462 : Vertex) [(394 : Vertex), (450 : Vertex), (456 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 89 = true ∨ valuation q 106 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value89, value106, value111, value113, value115, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(394 : Vertex), (450 : Vertex), (456 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (474 : Vertex) [(394 : Vertex), (450 : Vertex), (456 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 90 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value90, value108, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (396 : Vertex) (452 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 90 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value90, value111, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (396 : Vertex) (456 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 108 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value108, value111, value114, value115, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(452 : Vertex), (456 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (396 : Vertex) [(452 : Vertex), (456 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 90 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value90, value111, value114, value115, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(396 : Vertex), (456 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (452 : Vertex) [(396 : Vertex), (456 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 90 = true ∨ valuation q 108 = true ∨ valuation q 115 = true := by
  rw [value90, value108, value114, value115, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(396 : Vertex), (452 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (456 : Vertex) [(396 : Vertex), (452 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 90 = true ∨ valuation q 108 = true ∨ valuation q 111 = true := by
  rw [value90, value108, value111, value114, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(396 : Vertex), (452 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (462 : Vertex) [(396 : Vertex), (452 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 92 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value92, value109, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (454 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 92 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value92, value109, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (454 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 92 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value92, value113, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value109, value113, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (454 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 94 = false ∨ valuation q 105 = false ∨ valuation q 117 = false := by
  rw [value94, value105, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (400 : Vertex) (448 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 116 = true ∨ valuation q 118 = true := by
  rw [value116, value117, value118, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(464 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (452 : Vertex) [(464 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 108 = true ∨ valuation q 118 = true := by
  rw [value108, value117, value118, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(452 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (464 : Vertex) [(452 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 108 = true ∨ valuation q 116 = true := by
  rw [value108, value116, value117, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(452 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (469 : Vertex) [(452 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value117, value118, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (468 : Vertex) (471 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 119 = true ∨ valuation q 123 = true := by
  rw [value118, value119, value123, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(471 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (468 : Vertex) [(471 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 110 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value110, value118, value119, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (455 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 118 = true ∨ valuation q 124 = true := by
  rw [value118, value119, value124, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(469 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (455 : Vertex) [(469 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 110 = true ∨ valuation q 124 = true := by
  rw [value110, value119, value124, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(455 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (469 : Vertex) [(455 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value110, value118, value119, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(455 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (479 : Vertex) [(455 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 100 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value100, value112, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (409 : Vertex) (457 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 100 = false ∨ valuation q 112 = false ∨ valuation q 123 = false := by
  rw [value100, value112, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (409 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 100 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value100, value120, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (409 : Vertex) (475 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 112 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value112, value120, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (457 : Vertex) (475 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 43 = false ∨ valuation q 101 = false ∨ valuation q 113 = false := by
  rw [value43, value101, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 43 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value43, value113, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E186.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112186
