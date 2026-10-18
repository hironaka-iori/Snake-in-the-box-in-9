import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 153 = false := by
  rw [value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (207 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 157 = false := by
  rw [value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (221 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 158 = false := by
  rw [value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (222 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 159 = false := by
  rw [value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (226 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 161 = false := by
  rw [value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (238 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 164 = false := by
  rw [value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (258 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 165 = false := by
  rw [value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (260 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 169 = false := by
  rw [value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (264 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 171 = false := by
  rw [value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (267 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 173 = false := by
  rw [value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (270 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 178 = false := by
  rw [value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (277 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 181 = false := by
  rw [value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (281 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 184 = false := by
  rw [value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (287 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 185 = false := by
  rw [value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (320 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 187 = false := by
  rw [value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (326 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 190 = false := by
  rw [value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (329 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 193 = false := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (335 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 194 = false := by
  rw [value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (337 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (349 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 201 = false := by
  rw [value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (350 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (384 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 211 = false := by
  rw [value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (399 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 213 = false := by
  rw [value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (401 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 219 = false := by
  rw [value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (413 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 220 = false := by
  rw [value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (414 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 223 = false := by
  rw [value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (486 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 226 = false := by
  rw [value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (495 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 227 = false := by
  rw [value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 228 = false := by
  rw [value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (498 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 233 = false := by
  rw [value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (509 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 234 = false := by
  rw [value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (510 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause672 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [119]) + (countLit q [120]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120])
  have hm := merge_left (literal (valuationOf q) (119)) (literal (valuationOf q) (235)) (countLit q [119]) (countLit q [120]) (count235 q) 1 (meaning119 q) (meaning235 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 235 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E207.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112207
