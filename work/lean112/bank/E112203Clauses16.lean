import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 232 = true ∨ valuation q 117 = true := by
  rw [value115, value117, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (509 : Vertex) [(510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 232 = true ∨ valuation q 116 = true := by
  rw [value115, value116, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(509 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (510 : Vertex) [(509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 233 = true ∨ valuation q 115 = true := by
  rw [value115, value116, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(508 : Vertex)] := by decide
  have hg := other_cover q (509 : Vertex) (493 : Vertex) [(508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 233 = true ∨ valuation q 108 = true := by
  rw [value108, value116, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(493 : Vertex)] := by decide
  have hg := other_cover q (509 : Vertex) (508 : Vertex) [(493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value113, value114, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (510 : Vertex) (502 : Vertex) (506 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 234 = true ∨ valuation q 114 = true ∨ valuation q 115 = true := by
  rw [value114, value115, value117, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (510 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(506 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (510 : Vertex) (502 : Vertex) [(506 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 234 = true ∨ valuation q 113 = true ∨ valuation q 115 = true := by
  rw [value113, value115, value117, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (510 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(502 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (510 : Vertex) (506 : Vertex) [(502 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 118 = false := by
  rw [value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (0 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 120 = false := by
  rw [value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (6 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 124 = false := by
  rw [value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (15 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 125 = false := by
  rw [value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (17 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 126 = false := by
  rw [value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (18 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 130 = false := by
  rw [value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (29 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 131 = false := by
  rw [value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (30 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 133 = false := by
  rw [value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (130 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 136 = false := by
  rw [value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (135 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 141 = false := by
  rw [value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (142 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (149 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 145 = false := by
  rw [value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (153 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 149 = false := by
  rw [value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (159 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 150 = false := by
  rw [value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (198 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 151 = false := by
  rw [value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (201 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 153 = false := by
  rw [value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (207 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 158 = false := by
  rw [value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (222 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 159 = false := by
  rw [value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (226 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 161 = false := by
  rw [value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (238 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 164 = false := by
  rw [value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (258 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 165 = false := by
  rw [value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (260 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 168 = false := by
  rw [value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (263 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 173 = false := by
  rw [value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (270 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 178 = false := by
  rw [value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (277 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 181 = false := by
  rw [value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (281 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block16 (q : Snake 81) (h : Conditions q) : B112E203.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112203
