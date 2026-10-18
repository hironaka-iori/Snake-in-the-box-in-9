import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 210 = false := by
  rw [value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 211 = false := by
  rw [value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (498 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 213 = false := by
  rw [value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (500 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 217 = false := by
  rw [value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (509 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 218 = false := by
  rw [value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (510 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause230 (q : Nat → Bool) : valuationOf q 112 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [111]) + (countLit q [112]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112])
  have hm := merge_right (literal (valuationOf q) (112)) (literal (valuationOf q) (219)) (countLit q [111]) (countLit q [112]) (count219 q) 1 (meaning112 q) (meaning219 q) hs
  change valuationOf q 112 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 219 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [111]) + (countLit q [112]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112])
  have hm := merge_left (literal (valuationOf q) (111)) (literal (valuationOf q) (219)) (countLit q [111]) (countLit q [112]) (count219 q) 1 (meaning111 q) (meaning219 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 219 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 112 = false ∨ valuationOf q 220 = true := by
  have hs : count219 q = (countLit q [111]) + (countLit q [112]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112])
  have hm := merge_two (literal (valuationOf q) (111)) (literal (valuationOf q) (112)) (literal (valuationOf q) (220)) (countLit q [111]) (countLit q [112]) (count219 q) 1 1 (meaning111 q) (meaning112 q) (meaning220 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 112 = false ∨ valuationOf q 220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 220 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [110]) (countLit q [111, 112]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 222 = true := by
  have hs : count221 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_right (literal (valuationOf q) (220)) (literal (valuationOf q) (222)) (countLit q [110]) (countLit q [111, 112]) (count221 q) 2 (meaning220 q) (meaning222 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 222 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 113 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [113]) + (countLit q [114, 115]) := List.countP_append (p := literal q) (l₁ := [113]) (l₂ := [114, 115])
  have hm := merge_left (literal (valuationOf q) (113)) (literal (valuationOf q) (225)) (countLit q [113]) (countLit q [114, 115]) (count225 q) 1 (meaning113 q) (meaning225 q) hs
  change valuationOf q 113 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 225 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (227)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 (meaning225 q) (meaning227 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 227 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (227)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 (meaning221 q) (meaning227 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 227 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 225 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_two (literal (valuationOf q) (221)) (literal (valuationOf q) (225)) (literal (valuationOf q) (228)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 1 (meaning221 q) (meaning225 q) (meaning228 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 225 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 225 = false ∨ valuation q 228 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (228)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 2 (meaning222 q) (meaning228 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 228 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [117]) + (countLit q [118]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118])
  have hm := merge_right (literal (valuationOf q) (118)) (literal (valuationOf q) (229)) (countLit q [117]) (countLit q [118]) (count229 q) 1 (meaning118 q) (meaning229 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 229 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [117]) + (countLit q [118]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118])
  have hm := merge_left (literal (valuationOf q) (117)) (literal (valuationOf q) (229)) (countLit q [117]) (countLit q [118]) (count229 q) 1 (meaning117 q) (meaning229 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 229 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 118 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [117]) + (countLit q [118]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118])
  have hm := merge_two (literal (valuationOf q) (117)) (literal (valuationOf q) (118)) (literal (valuationOf q) (230)) (countLit q [117]) (countLit q [118]) (count229 q) 1 1 (meaning117 q) (meaning118 q) (meaning230 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 118 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 230 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [116]) + (countLit q [117, 118]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117, 118])
  have hm := merge_right (literal (valuationOf q) (229)) (literal (valuationOf q) (231)) (countLit q [116]) (countLit q [117, 118]) (count231 q) 1 (meaning229 q) (meaning231 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 231 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 232 = true := by
  have hs : count231 q = (countLit q [116]) + (countLit q [117, 118]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117, 118])
  have hm := merge_right (literal (valuationOf q) (230)) (literal (valuationOf q) (232)) (countLit q [116]) (countLit q [117, 118]) (count231 q) 2 (meaning230 q) (meaning232 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 232 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 232 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [119]) + (countLit q [120]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120])
  have hm := merge_left (literal (valuationOf q) (119)) (literal (valuationOf q) (233)) (countLit q [119]) (countLit q [120]) (count233 q) 1 (meaning119 q) (meaning233 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 233 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [119, 120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [119, 120]) (l₂ := [121, 122])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (237)) (countLit q [119, 120]) (countLit q [121, 122]) (count237 q) 1 (meaning233 q) (meaning237 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 237 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [116, 117, 118]) + (countLit q [119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 120, 121, 122])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [116, 117, 118]) (countLit q [119, 120, 121, 122]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [116, 117, 118]) + (countLit q [119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (239)) (countLit q [116, 117, 118]) (countLit q [119, 120, 121, 122]) (count239 q) 1 (meaning231 q) (meaning239 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 239 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [116, 117, 118]) + (countLit q [119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 120, 121, 122])
  have hm := merge_two (literal (valuationOf q) (231)) (literal (valuationOf q) (237)) (literal (valuationOf q) (240)) (countLit q [116, 117, 118]) (countLit q [119, 120, 121, 122]) (count239 q) 1 1 (meaning231 q) (meaning237 q) (meaning240 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 237 = false ∨ valuation q 240 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [116, 117, 118]) + (countLit q [119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (232)) (literal (valuationOf q) (240)) (countLit q [116, 117, 118]) (countLit q [119, 120, 121, 122]) (count239 q) 2 (meaning232 q) (meaning240 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 240 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122])
  have hm := merge_right (literal (valuationOf q) (240)) (literal (valuationOf q) (242)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122]) (count241 q) 2 (meaning240 q) (meaning242 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 242 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (241)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122]) (count241 q) 1 (meaning227 q) (meaning241 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 241 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 239 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122])
  have hm := merge_two (literal (valuationOf q) (227)) (literal (valuationOf q) (239)) (literal (valuationOf q) (242)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122]) (count241 q) 1 1 (meaning227 q) (meaning239 q) (meaning242 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 239 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 239 = false ∨ valuation q 242 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (228)) (literal (valuationOf q) (242)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122]) (count241 q) 2 (meaning228 q) (meaning242 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 242 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (243)) (countLit q [124]) (countLit q [125]) (count243 q) 1 (meaning124 q) (meaning243 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 243 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E201.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112201
