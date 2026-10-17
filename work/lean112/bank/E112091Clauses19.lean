import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1281 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1277)) (literal (valuationOf q) (1281)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 1 (meaning1277 q) (meaning1281 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1281 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1282 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1278)) (literal (valuationOf q) (1282)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 2 (meaning1278 q) (meaning1282 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1282 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1279 = false ∨ valuationOf q 1283 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1279)) (literal (valuationOf q) (1283)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 3 (meaning1279 q) (meaning1283 q) hs
  change valuationOf q 1279 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1279 = false ∨ valuation q 1283 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1281 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_left (literal (valuationOf q) (1270)) (literal (valuationOf q) (1281)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 1 (meaning1270 q) (meaning1281 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1281 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1282 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1277)) (literal (valuationOf q) (1282)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 1 1 (meaning1270 q) (meaning1277 q) (meaning1282 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1277 = false ∨ valuation q 1282 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1283 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1278)) (literal (valuationOf q) (1283)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 1 2 (meaning1270 q) (meaning1278 q) (meaning1283 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1278 = false ∨ valuation q 1283 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1279 = false ∨ valuationOf q 1284 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1279)) (literal (valuationOf q) (1284)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 1 3 (meaning1270 q) (meaning1279 q) (meaning1284 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1279 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1279 = false ∨ valuation q 1284 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1282 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_left (literal (valuationOf q) (1271)) (literal (valuationOf q) (1282)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 2 (meaning1271 q) (meaning1282 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1282 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1283 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1277)) (literal (valuationOf q) (1283)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 2 1 (meaning1271 q) (meaning1277 q) (meaning1283 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1277 = false ∨ valuation q 1283 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1284 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1278)) (literal (valuationOf q) (1284)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 2 2 (meaning1271 q) (meaning1278 q) (meaning1284 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1278 = false ∨ valuation q 1284 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1279 = false ∨ valuationOf q 1285 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1279)) (literal (valuationOf q) (1285)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 2 3 (meaning1271 q) (meaning1279 q) (meaning1285 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1279 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1279 = false ∨ valuation q 1285 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1284 = true := by
  have hs : count1281 q = (countLit q [-11, -14, -15]) + (countLit q [-18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-11, -14, -15]) (l₂ := [-18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1277)) (literal (valuationOf q) (1284)) (countLit q [-11, -14, -15]) (countLit q [-18, -20, -23, -25]) (count1281 q) 3 1 (meaning1272 q) (meaning1277 q) (meaning1284 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1277 = false ∨ valuation q 1284 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1281)) (literal (valuationOf q) (1288)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 1 (meaning1281 q) (meaning1288 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1288 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1282 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1282)) (literal (valuationOf q) (1289)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 2 (meaning1282 q) (meaning1289 q) hs
  change valuationOf q 1282 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1282 = false ∨ valuation q 1289 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1283)) (literal (valuationOf q) (1290)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 3 (meaning1283 q) (meaning1290 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1290 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1284)) (literal (valuationOf q) (1291)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 4 (meaning1284 q) (meaning1291 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1291 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1292 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1285)) (literal (valuationOf q) (1292)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 5 (meaning1285 q) (meaning1292 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1292 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_left (literal (valuationOf q) (1262)) (literal (valuationOf q) (1288)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 1 (meaning1262 q) (meaning1288 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1288 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1289)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 1 1 (meaning1262 q) (meaning1281 q) (meaning1289 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1281 = false ∨ valuation q 1289 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1290)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 1 2 (meaning1262 q) (meaning1282 q) (meaning1290 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1282 = false ∨ valuation q 1290 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1291)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 1 3 (meaning1262 q) (meaning1283 q) (meaning1291 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1283 = false ∨ valuation q 1291 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_left (literal (valuationOf q) (1263)) (literal (valuationOf q) (1289)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 2 (meaning1263 q) (meaning1289 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1289 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1290)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 2 1 (meaning1263 q) (meaning1281 q) (meaning1290 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1281 = false ∨ valuation q 1290 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1291)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 2 2 (meaning1263 q) (meaning1282 q) (meaning1291 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1282 = false ∨ valuation q 1291 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1292 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1292)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 2 3 (meaning1263 q) (meaning1283 q) (meaning1292 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1283 = false ∨ valuation q 1292 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_left (literal (valuationOf q) (1264)) (literal (valuationOf q) (1290)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 3 (meaning1264 q) (meaning1290 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1290 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -7, -8, -9, -10]) + (countLit q [-11, -14, -15, -18, -20, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10]) (l₂ := [-11, -14, -15, -18, -20, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1291)) (countLit q [-2, -4, -7, -8, -9, -10]) (countLit q [-11, -14, -15, -18, -20, -23, -25]) (count1288 q) 3 1 (meaning1264 q) (meaning1281 q) (meaning1291 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1281 = false ∨ valuation q 1291 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1301)) (countLit q [-29]) (countLit q [-30]) (count1301 q) 1 (meaningNeg30 q) (meaning1301 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1301 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1301)) (countLit q [-29]) (countLit q [-30]) (count1301 q) 1 (meaningNeg29 q) (meaning1301 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1301 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1302)) (countLit q [-29]) (countLit q [-30]) (count1301 q) 1 1 (meaningNeg29 q) (meaningNeg30 q) (meaning1302 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 1302 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1303 = true := by
  have hs : count1303 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1301)) (literal (valuationOf q) (1303)) (countLit q [-27]) (countLit q [-29, -30]) (count1303 q) 1 (meaning1301 q) (meaning1303 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1303 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1304 = true := by
  have hs : count1303 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1302)) (literal (valuationOf q) (1304)) (countLit q [-27]) (countLit q [-29, -30]) (count1303 q) 2 (meaning1302 q) (meaning1304 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1304 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E091.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112091
