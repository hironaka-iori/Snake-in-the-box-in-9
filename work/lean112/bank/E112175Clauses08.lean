import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 176 = false := by
  rw [value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (349 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 177 = false := by
  rw [value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (350 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 178 = false := by
  rw [value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (390 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 180 = false := by
  rw [value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (393 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 182 = false := by
  rw [value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (399 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 186 = false := by
  rw [value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (413 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 187 = false := by
  rw [value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (414 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 188 = false := by
  rw [value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (418 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 192 = false := by
  rw [value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (430 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 193 = false := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (480 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 195 = false := by
  rw [value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (486 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 198 = false := by
  rw [value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (489 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (495 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 201 = false := by
  rw [value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause271 (q : Nat → Bool) : valuationOf q 106 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [106]) + (countLit q [107]) := List.countP_append (p := literal q) (l₁ := [106]) (l₂ := [107])
  have hm := merge_left (literal (valuationOf q) (106)) (literal (valuationOf q) (209)) (countLit q [106]) (countLit q [107]) (count209 q) 1 (meaning106 q) (meaning209 q) hs
  change valuationOf q 106 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 209 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [105]) + (countLit q [106, 107]) := List.countP_append (p := literal q) (l₁ := [105]) (l₂ := [106, 107])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (211)) (countLit q [105]) (countLit q [106, 107]) (count211 q) 1 (meaning209 q) (meaning211 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 211 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 110 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [109]) + (countLit q [110]) := List.countP_append (p := literal q) (l₁ := [109]) (l₂ := [110])
  have hm := merge_right (literal (valuationOf q) (110)) (literal (valuationOf q) (213)) (countLit q [109]) (countLit q [110]) (count213 q) 1 (meaning110 q) (meaning213 q) hs
  change valuationOf q 110 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 213 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [108]) + (countLit q [109, 110]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109, 110])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (215)) (countLit q [108]) (countLit q [109, 110]) (count215 q) 1 (meaning213 q) (meaning215 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 215 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning215 q) (meaning217 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 217 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_left (literal (valuationOf q) (211)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning211 q) (meaning217 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 217 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [111]) + (countLit q [112, 113]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112, 113])
  have hm := merge_left (literal (valuationOf q) (111)) (literal (valuationOf q) (221)) (countLit q [111]) (countLit q [112, 113]) (count221 q) 1 (meaning111 q) (meaning221 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 221 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (227)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 (meaning221 q) (meaning227 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 227 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning217 q) (meaning229 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 229 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_two (literal (valuationOf q) (217)) (literal (valuationOf q) (227)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 1 (meaning217 q) (meaning227 q) (meaning230 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 227 = false ∨ valuation q 230 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_right (literal (valuationOf q) (119)) (literal (valuationOf q) (231)) (countLit q [118]) (countLit q [119]) (count231 q) 1 (meaning119 q) (meaning231 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 231 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [117]) (countLit q [118, 119]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_left (literal (valuationOf q) (117)) (literal (valuationOf q) (233)) (countLit q [117]) (countLit q [118, 119]) (count233 q) 1 (meaning117 q) (meaning233 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 233 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (239)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122]) (count239 q) 1 (meaning233 q) (meaning239 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 239 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_right (literal (valuationOf q) (125)) (literal (valuationOf q) (241)) (countLit q [124]) (countLit q [125]) (count241 q) 1 (meaning125 q) (meaning241 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 241 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [123]) (countLit q [124, 125]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_right (literal (valuationOf q) (127)) (literal (valuationOf q) (245)) (countLit q [126]) (countLit q [127]) (count245 q) 1 (meaning127 q) (meaning245 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 245 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E175.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112175
