import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 108 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [108]) + (countLit q [109]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109])
  have hm := merge_left (literal (valuationOf q) (108)) (literal (valuationOf q) (213)) (countLit q [108]) (countLit q [109]) (count213 q) 1 (meaning108 q) (meaning213 q) hs
  change valuationOf q 108 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 213 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [107]) + (countLit q [108, 109]) := List.countP_append (p := literal q) (l₁ := [107]) (l₂ := [108, 109])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (215)) (countLit q [107]) (countLit q [108, 109]) (count215 q) 1 (meaning213 q) (meaning215 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 215 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 110 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_left (literal (valuationOf q) (110)) (literal (valuationOf q) (219)) (countLit q [110]) (countLit q [111, 112]) (count219 q) 1 (meaning110 q) (meaning219 q) hs
  change valuationOf q 110 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 219 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [107, 108, 109]) + (countLit q [110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109]) (l₂ := [110, 111, 112])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [107, 108, 109]) (countLit q [110, 111, 112]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [107, 108, 109]) + (countLit q [110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109]) (l₂ := [110, 111, 112])
  have hm := merge_left (literal (valuationOf q) (215)) (literal (valuationOf q) (221)) (countLit q [107, 108, 109]) (countLit q [110, 111, 112]) (count221 q) 1 (meaning215 q) (meaning221 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 221 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 115 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [114]) + (countLit q [115]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115])
  have hm := merge_right (literal (valuationOf q) (115)) (literal (valuationOf q) (223)) (countLit q [114]) (countLit q [115]) (count223 q) 1 (meaning115 q) (meaning223 q) hs
  change valuationOf q 115 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 223 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 114 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [114]) + (countLit q [115]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115])
  have hm := merge_left (literal (valuationOf q) (114)) (literal (valuationOf q) (223)) (countLit q [114]) (countLit q [115]) (count223 q) 1 (meaning114 q) (meaning223 q) hs
  change valuationOf q 114 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 223 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [113]) + (countLit q [114, 115]) := List.countP_append (p := literal q) (l₁ := [113]) (l₂ := [114, 115])
  have hm := merge_right (literal (valuationOf q) (223)) (literal (valuationOf q) (225)) (countLit q [113]) (countLit q [114, 115]) (count225 q) 1 (meaning223 q) (meaning225 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 225 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 113 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [113]) + (countLit q [114, 115]) := List.countP_append (p := literal q) (l₁ := [113]) (l₂ := [114, 115])
  have hm := merge_left (literal (valuationOf q) (113)) (literal (valuationOf q) (225)) (countLit q [113]) (countLit q [114, 115]) (count225 q) 1 (meaning113 q) (meaning225 q) hs
  change valuationOf q 113 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 225 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [116]) + (countLit q [117]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117])
  have hm := merge_right (literal (valuationOf q) (117)) (literal (valuationOf q) (227)) (countLit q [116]) (countLit q [117]) (count227 q) 1 (meaning117 q) (meaning227 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 227 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 116 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [116]) + (countLit q [117]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117])
  have hm := merge_left (literal (valuationOf q) (116)) (literal (valuationOf q) (227)) (countLit q [116]) (countLit q [117]) (count227 q) 1 (meaning116 q) (meaning227 q) hs
  change valuationOf q 116 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 227 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 116 = false ∨ valuationOf q 117 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [116]) + (countLit q [117]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117])
  have hm := merge_two (literal (valuationOf q) (116)) (literal (valuationOf q) (117)) (literal (valuationOf q) (228)) (countLit q [116]) (countLit q [117]) (count227 q) 1 1 (meaning116 q) (meaning117 q) (meaning228 q) hs
  change valuationOf q 116 = false ∨ valuationOf q 117 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 228 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [116, 117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [116, 117]) (l₂ := [118, 119])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (231)) (countLit q [116, 117]) (countLit q [118, 119]) (count231 q) 1 (meaning227 q) (meaning231 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 231 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 232 = true := by
  have hs : count231 q = (countLit q [116, 117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [116, 117]) (l₂ := [118, 119])
  have hm := merge_left (literal (valuationOf q) (228)) (literal (valuationOf q) (232)) (countLit q [116, 117]) (countLit q [118, 119]) (count231 q) 2 (meaning228 q) (meaning232 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 232 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 232 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [113, 114, 115]) + (countLit q [116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [113, 114, 115]) (l₂ := [116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [113, 114, 115]) (countLit q [116, 117, 118, 119]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 234 = true := by
  have hs : count233 q = (countLit q [113, 114, 115]) + (countLit q [116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [113, 114, 115]) (l₂ := [116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (232)) (literal (valuationOf q) (234)) (countLit q [113, 114, 115]) (countLit q [116, 117, 118, 119]) (count233 q) 2 (meaning232 q) (meaning234 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 234 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [113, 114, 115]) + (countLit q [116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [113, 114, 115]) (l₂ := [116, 117, 118, 119])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (233)) (countLit q [113, 114, 115]) (countLit q [116, 117, 118, 119]) (count233 q) 1 (meaning225 q) (meaning233 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 233 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 231 = false ∨ valuationOf q 234 = true := by
  have hs : count233 q = (countLit q [113, 114, 115]) + (countLit q [116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [113, 114, 115]) (l₂ := [116, 117, 118, 119])
  have hm := merge_two (literal (valuationOf q) (225)) (literal (valuationOf q) (231)) (literal (valuationOf q) (234)) (countLit q [113, 114, 115]) (countLit q [116, 117, 118, 119]) (count233 q) 1 1 (meaning225 q) (meaning231 q) (meaning234 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 231 = false ∨ valuationOf q 234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 231 = false ∨ valuation q 234 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 236 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (236)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 2 (meaning234 q) (meaning236 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 236 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (235)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 1 (meaning221 q) (meaning235 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 235 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 233 = false ∨ valuationOf q 236 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_two (literal (valuationOf q) (221)) (literal (valuationOf q) (233)) (literal (valuationOf q) (236)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 1 1 (meaning221 q) (meaning233 q) (meaning236 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 233 = false ∨ valuationOf q 236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 233 = false ∨ valuation q 236 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_left (literal (valuationOf q) (121)) (literal (valuationOf q) (237)) (countLit q [121]) (countLit q [122]) (count237 q) 1 (meaning121 q) (meaning237 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 237 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [120]) (countLit q [121, 122]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (239)) (countLit q [120]) (countLit q [121, 122]) (count239 q) 1 (meaning120 q) (meaning239 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 239 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_two (literal (valuationOf q) (120)) (literal (valuationOf q) (237)) (literal (valuationOf q) (240)) (countLit q [120]) (countLit q [121, 122]) (count239 q) 1 1 (meaning120 q) (meaning237 q) (meaning240 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 237 = false ∨ valuation q 240 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (241)) (countLit q [124]) (countLit q [125]) (count241 q) 1 (meaning124 q) (meaning241 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 241 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [123]) (countLit q [124, 125]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [120, 121, 122]) + (countLit q [123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122]) (l₂ := [123, 124, 125])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [120, 121, 122]) (countLit q [123, 124, 125]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [120, 121, 122]) + (countLit q [123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122]) (l₂ := [123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (245)) (countLit q [120, 121, 122]) (countLit q [123, 124, 125]) (count245 q) 1 (meaning239 q) (meaning245 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 245 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 246 = true := by
  have hs : count245 q = (countLit q [120, 121, 122]) + (countLit q [123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122]) (l₂ := [123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (240)) (literal (valuationOf q) (246)) (countLit q [120, 121, 122]) (countLit q [123, 124, 125]) (count245 q) 2 (meaning240 q) (meaning246 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 246 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127, 128])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (249)) (countLit q [126]) (countLit q [127, 128]) (count249 q) 1 (meaning126 q) (meaning249 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 249 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E091.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112091
