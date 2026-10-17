import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1233 = true := by
  have hs : count1233 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1233)) (countLit q [-24]) (countLit q [-25]) (count1233 q) 1 (meaningNeg25 q) (meaning1233 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1233 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1233 = true := by
  have hs : count1233 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1233)) (countLit q [-24]) (countLit q [-25]) (count1233 q) 1 (meaningNeg24 q) (meaning1233 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1233 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1234 = true := by
  have hs : count1233 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1234)) (countLit q [-24]) (countLit q [-25]) (count1233 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning1234 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 1234 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1235 = true := by
  have hs : count1235 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (1233)) (literal (valuationOf q) (1235)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count1235 q) 1 (meaning1233 q) (meaning1235 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1235 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1236 = true := by
  have hs : count1235 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (1234)) (literal (valuationOf q) (1236)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count1235 q) 2 (meaning1234 q) (meaning1236 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1236 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1235 = true := by
  have hs : count1235 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_left (literal (valuationOf q) (1231)) (literal (valuationOf q) (1235)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count1235 q) 1 (meaning1231 q) (meaning1235 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1235 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1233 = false ∨ valuationOf q 1236 = true := by
  have hs : count1235 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (1231)) (literal (valuationOf q) (1233)) (literal (valuationOf q) (1236)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count1235 q) 1 1 (meaning1231 q) (meaning1233 q) (meaning1236 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1233 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1233 = false ∨ valuation q 1236 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1234 = false ∨ valuationOf q 1237 = true := by
  have hs : count1235 q = (countLit q [-20, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (1231)) (literal (valuationOf q) (1234)) (literal (valuationOf q) (1237)) (countLit q [-20, -22]) (countLit q [-24, -25]) (count1235 q) 1 2 (meaning1231 q) (meaning1234 q) (meaning1237 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1234 = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1234 = false ∨ valuation q 1237 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-13, -15, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (1235)) (literal (valuationOf q) (1239)) (countLit q [-13, -15, -17]) (countLit q [-20, -22, -24, -25]) (count1239 q) 1 (meaning1235 q) (meaning1239 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1239 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 1236 = false ∨ valuationOf q 1240 = true := by
  have hs : count1239 q = (countLit q [-13, -15, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (1236)) (literal (valuationOf q) (1240)) (countLit q [-13, -15, -17]) (countLit q [-20, -22, -24, -25]) (count1239 q) 2 (meaning1236 q) (meaning1240 q) hs
  change valuationOf q 1236 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1236 = false ∨ valuation q 1240 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 1237 = false ∨ valuationOf q 1241 = true := by
  have hs : count1239 q = (countLit q [-13, -15, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (1237)) (literal (valuationOf q) (1241)) (countLit q [-13, -15, -17]) (countLit q [-20, -22, -24, -25]) (count1239 q) 3 (meaning1237 q) (meaning1241 q) hs
  change valuationOf q 1237 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 1237 = false ∨ valuation q 1241 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-13, -15, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (1228)) (literal (valuationOf q) (1239)) (countLit q [-13, -15, -17]) (countLit q [-20, -22, -24, -25]) (count1239 q) 1 (meaning1228 q) (meaning1239 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1239 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1240 = true := by
  have hs : count1239 q = (countLit q [-13, -15, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1228)) (literal (valuationOf q) (1235)) (literal (valuationOf q) (1240)) (countLit q [-13, -15, -17]) (countLit q [-20, -22, -24, -25]) (count1239 q) 1 1 (meaning1228 q) (meaning1235 q) (meaning1240 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1235 = false ∨ valuation q 1240 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1236 = false ∨ valuationOf q 1241 = true := by
  have hs : count1239 q = (countLit q [-13, -15, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1228)) (literal (valuationOf q) (1236)) (literal (valuationOf q) (1241)) (countLit q [-13, -15, -17]) (countLit q [-20, -22, -24, -25]) (count1239 q) 1 2 (meaning1228 q) (meaning1236 q) (meaning1241 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1236 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1236 = false ∨ valuation q 1241 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 1229 = false ∨ valuationOf q 1240 = true := by
  have hs : count1239 q = (countLit q [-13, -15, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (1229)) (literal (valuationOf q) (1240)) (countLit q [-13, -15, -17]) (countLit q [-20, -22, -24, -25]) (count1239 q) 2 (meaning1229 q) (meaning1240 q) hs
  change valuationOf q 1229 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 1229 = false ∨ valuation q 1240 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 1229 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1241 = true := by
  have hs : count1239 q = (countLit q [-13, -15, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1229)) (literal (valuationOf q) (1235)) (literal (valuationOf q) (1241)) (countLit q [-13, -15, -17]) (countLit q [-20, -22, -24, -25]) (count1239 q) 2 1 (meaning1229 q) (meaning1235 q) (meaning1241 q) hs
  change valuationOf q 1229 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 1229 = false ∨ valuation q 1235 = false ∨ valuation q 1241 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 1240 = false ∨ valuationOf q 1247 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (1240)) (literal (valuationOf q) (1247)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 2 (meaning1240 q) (meaning1247 q) hs
  change valuationOf q 1240 = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 1240 = false ∨ valuation q 1247 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1248 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (1241)) (literal (valuationOf q) (1248)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 3 (meaning1241 q) (meaning1248 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1248 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 1220 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1247 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1220)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1247)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 1 1 (meaning1220 q) (meaning1239 q) (meaning1247 q) hs
  change valuationOf q 1220 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 1220 = false ∨ valuation q 1239 = false ∨ valuation q 1247 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 1220 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1248 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1220)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1248)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 1 2 (meaning1220 q) (meaning1240 q) (meaning1248 q) hs
  change valuationOf q 1220 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 1220 = false ∨ valuation q 1240 = false ∨ valuation q 1248 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 1220 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1249 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1220)) (literal (valuationOf q) (1241)) (literal (valuationOf q) (1249)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 1 3 (meaning1220 q) (meaning1241 q) (meaning1249 q) hs
  change valuationOf q 1220 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 1220 = false ∨ valuation q 1241 = false ∨ valuation q 1249 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1247 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (1221)) (literal (valuationOf q) (1247)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 2 (meaning1221 q) (meaning1247 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1247 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1248 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1221)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1248)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 2 1 (meaning1221 q) (meaning1239 q) (meaning1248 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1239 = false ∨ valuation q 1248 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1249 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1221)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1249)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 2 2 (meaning1221 q) (meaning1240 q) (meaning1249 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1240 = false ∨ valuation q 1249 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1248 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (1222)) (literal (valuationOf q) (1248)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 3 (meaning1222 q) (meaning1248 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1248 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1249 = true := by
  have hs : count1246 q = (countLit q [-3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1222)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1249)) (countLit q [-3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -17, -20, -22, -24, -25]) (count1246 q) 3 1 (meaning1222 q) (meaning1239 q) (meaning1249 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1239 = false ∨ valuation q 1249 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1259)) (countLit q [-29]) (countLit q [-31]) (count1259 q) 1 (meaningNeg31 q) (meaning1259 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1259 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1259)) (countLit q [-29]) (countLit q [-31]) (count1259 q) 1 (meaningNeg29 q) (meaning1259 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1259 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1260)) (countLit q [-29]) (countLit q [-31]) (count1259 q) 1 1 (meaningNeg29 q) (meaningNeg31 q) (meaning1260 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 31 = true ∨ valuation q 1260 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1259)) (literal (valuationOf q) (1261)) (countLit q [-28]) (countLit q [-29, -31]) (count1261 q) 1 (meaning1259 q) (meaning1261 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1261 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1262 = true := by
  have hs : count1261 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1260)) (literal (valuationOf q) (1262)) (countLit q [-28]) (countLit q [-29, -31]) (count1261 q) 2 (meaning1260 q) (meaning1262 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1262 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1261)) (countLit q [-28]) (countLit q [-29, -31]) (count1261 q) 1 (meaningNeg28 q) (meaning1261 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1261 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E094.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112094
