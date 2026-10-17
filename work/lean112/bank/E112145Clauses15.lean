import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1243 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1234)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1243)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 1 1 (meaning1234 q) (meaning1239 q) (meaning1243 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1239 = false ∨ valuation q 1243 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1244 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1234)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1244)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 1 2 (meaning1234 q) (meaning1240 q) (meaning1244 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1240 = false ∨ valuation q 1244 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1243 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1235)) (literal (valuationOf q) (1243)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 2 (meaning1235 q) (meaning1243 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1243 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1244 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1235)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1244)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 2 1 (meaning1235 q) (meaning1239 q) (meaning1244 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1239 = false ∨ valuation q 1244 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1245 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1235)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1245)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 2 2 (meaning1235 q) (meaning1240 q) (meaning1245 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1240 = false ∨ valuation q 1245 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1236 = false ∨ valuationOf q 1244 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1236)) (literal (valuationOf q) (1244)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 3 (meaning1236 q) (meaning1244 q) hs
  change valuationOf q 1236 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1236 = false ∨ valuation q 1244 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1236 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1246 = true := by
  have hs : count1242 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1236)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1246)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1242 q) 3 2 (meaning1236 q) (meaning1240 q) (meaning1246 q) hs
  change valuationOf q 1236 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1236 = false ∨ valuation q 1240 = false ∨ valuation q 1246 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1248)) (countLit q [-16]) (countLit q [-18]) (count1248 q) 1 (meaningNeg18 q) (meaning1248 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1248 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1248)) (countLit q [-16]) (countLit q [-18]) (count1248 q) 1 (meaningNeg16 q) (meaning1248 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1248 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1249 = true := by
  have hs : count1248 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1249)) (countLit q [-16]) (countLit q [-18]) (count1248 q) 1 1 (meaningNeg16 q) (meaningNeg18 q) (meaning1249 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 1249 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1250 = true := by
  have hs : count1250 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_right (literal (valuationOf q) (1248)) (literal (valuationOf q) (1250)) (countLit q [-14]) (countLit q [-16, -18]) (count1250 q) 1 (meaning1248 q) (meaning1250 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1250 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1251 = true := by
  have hs : count1250 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_right (literal (valuationOf q) (1249)) (literal (valuationOf q) (1251)) (countLit q [-14]) (countLit q [-16, -18]) (count1250 q) 2 (meaning1249 q) (meaning1251 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1251 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1250 = true := by
  have hs : count1250 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1250)) (countLit q [-14]) (countLit q [-16, -18]) (count1250 q) 1 (meaningNeg14 q) (meaning1250 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1250 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1248 = false ∨ valuationOf q 1251 = true := by
  have hs : count1250 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1251)) (countLit q [-14]) (countLit q [-16, -18]) (count1250 q) 1 1 (meaningNeg14 q) (meaning1248 q) (meaning1251 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1248 = false ∨ valuation q 1251 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1249 = false ∨ valuationOf q 1252 = true := by
  have hs : count1250 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1252)) (countLit q [-14]) (countLit q [-16, -18]) (count1250 q) 1 2 (meaningNeg14 q) (meaning1249 q) (meaning1252 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1249 = false ∨ valuation q 1252 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1253 = true := by
  have hs : count1253 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1253)) (countLit q [-23]) (countLit q [-24]) (count1253 q) 1 (meaningNeg24 q) (meaning1253 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1253 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1253 = true := by
  have hs : count1253 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1253)) (countLit q [-23]) (countLit q [-24]) (count1253 q) 1 (meaningNeg23 q) (meaning1253 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1253 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1254 = true := by
  have hs : count1253 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1254)) (countLit q [-23]) (countLit q [-24]) (count1253 q) 1 1 (meaningNeg23 q) (meaningNeg24 q) (meaning1254 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 1254 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1255 = true := by
  have hs : count1255 q = (countLit q [-21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23, -24])
  have hm := merge_right (literal (valuationOf q) (1253)) (literal (valuationOf q) (1255)) (countLit q [-21]) (countLit q [-23, -24]) (count1255 q) 1 (meaning1253 q) (meaning1255 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1255 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1256 = true := by
  have hs : count1255 q = (countLit q [-21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23, -24])
  have hm := merge_right (literal (valuationOf q) (1254)) (literal (valuationOf q) (1256)) (countLit q [-21]) (countLit q [-23, -24]) (count1255 q) 2 (meaning1254 q) (meaning1256 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1256 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1255 = true := by
  have hs : count1255 q = (countLit q [-21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23, -24])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1255)) (countLit q [-21]) (countLit q [-23, -24]) (count1255 q) 1 (meaningNeg21 q) (meaning1255 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1255 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1253 = false ∨ valuationOf q 1256 = true := by
  have hs : count1255 q = (countLit q [-21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (1253)) (literal (valuationOf q) (1256)) (countLit q [-21]) (countLit q [-23, -24]) (count1255 q) 1 1 (meaningNeg21 q) (meaning1253 q) (meaning1256 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1256 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1253 = false ∨ valuation q 1256 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1254 = false ∨ valuationOf q 1257 = true := by
  have hs : count1255 q = (countLit q [-21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (1254)) (literal (valuationOf q) (1257)) (countLit q [-21]) (countLit q [-23, -24]) (count1255 q) 1 2 (meaningNeg21 q) (meaning1254 q) (meaning1257 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1254 = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1254 = false ∨ valuation q 1257 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1258 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1255)) (literal (valuationOf q) (1258)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 1 (meaning1255 q) (meaning1258 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1258 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 1256 = false ∨ valuationOf q 1259 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1256)) (literal (valuationOf q) (1259)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 2 (meaning1256 q) (meaning1259 q) hs
  change valuationOf q 1256 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 1256 = false ∨ valuation q 1259 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1258 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1250)) (literal (valuationOf q) (1258)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 1 (meaning1250 q) (meaning1258 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1258 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1259 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1250)) (literal (valuationOf q) (1255)) (literal (valuationOf q) (1259)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 1 1 (meaning1250 q) (meaning1255 q) (meaning1259 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1255 = false ∨ valuation q 1259 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1256 = false ∨ valuationOf q 1260 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1250)) (literal (valuationOf q) (1256)) (literal (valuationOf q) (1260)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 1 2 (meaning1250 q) (meaning1256 q) (meaning1260 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1256 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1256 = false ∨ valuation q 1260 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1259 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1251)) (literal (valuationOf q) (1259)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 2 (meaning1251 q) (meaning1259 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1259 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1260 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1255)) (literal (valuationOf q) (1260)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 2 1 (meaning1251 q) (meaning1255 q) (meaning1260 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1255 = false ∨ valuation q 1260 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1256 = false ∨ valuationOf q 1261 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1256)) (literal (valuationOf q) (1261)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 2 2 (meaning1251 q) (meaning1256 q) (meaning1261 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1256 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1256 = false ∨ valuation q 1261 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1260 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1252)) (literal (valuationOf q) (1260)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 3 (meaning1252 q) (meaning1260 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1260 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E145.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112145
