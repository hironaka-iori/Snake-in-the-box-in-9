import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1280)) (countLit q [-32]) (countLit q [-35]) (count1280 q) 1 (meaningNeg35 q) (meaning1280 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1280 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1280)) (countLit q [-32]) (countLit q [-35]) (count1280 q) 1 (meaningNeg32 q) (meaning1280 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1280 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1281 = true := by
  have hs : count1280 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1281)) (countLit q [-32]) (countLit q [-35]) (count1280 q) 1 1 (meaningNeg32 q) (meaningNeg35 q) (meaning1281 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 35 = true ∨ valuation q 1281 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1282 = true := by
  have hs : count1282 q = (countLit q [-31]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32, -35])
  have hm := merge_right (literal (valuationOf q) (1280)) (literal (valuationOf q) (1282)) (countLit q [-31]) (countLit q [-32, -35]) (count1282 q) 1 (meaning1280 q) (meaning1282 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1282 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1283 = true := by
  have hs : count1282 q = (countLit q [-31]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32, -35])
  have hm := merge_right (literal (valuationOf q) (1281)) (literal (valuationOf q) (1283)) (countLit q [-31]) (countLit q [-32, -35]) (count1282 q) 2 (meaning1281 q) (meaning1283 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1283 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1282 = true := by
  have hs : count1282 q = (countLit q [-31]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32, -35])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1282)) (countLit q [-31]) (countLit q [-32, -35]) (count1282 q) 1 (meaningNeg31 q) (meaning1282 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1282 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1280 = false ∨ valuationOf q 1283 = true := by
  have hs : count1282 q = (countLit q [-31]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32, -35])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (1280)) (literal (valuationOf q) (1283)) (countLit q [-31]) (countLit q [-32, -35]) (count1282 q) 1 1 (meaningNeg31 q) (meaning1280 q) (meaning1283 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1280 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1280 = false ∨ valuation q 1283 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 1282 = false ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-25, -29, -30]) + (countLit q [-31, -32, -35]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30]) (l₂ := [-31, -32, -35])
  have hm := merge_right (literal (valuationOf q) (1282)) (literal (valuationOf q) (1285)) (countLit q [-25, -29, -30]) (countLit q [-31, -32, -35]) (count1285 q) 1 (meaning1282 q) (meaning1285 q) hs
  change valuationOf q 1282 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 1282 = false ∨ valuation q 1285 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1286 = true := by
  have hs : count1285 q = (countLit q [-25, -29, -30]) + (countLit q [-31, -32, -35]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30]) (l₂ := [-31, -32, -35])
  have hm := merge_right (literal (valuationOf q) (1283)) (literal (valuationOf q) (1286)) (countLit q [-25, -29, -30]) (countLit q [-31, -32, -35]) (count1285 q) 2 (meaning1283 q) (meaning1286 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1286 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-25, -29, -30]) + (countLit q [-31, -32, -35]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30]) (l₂ := [-31, -32, -35])
  have hm := merge_left (literal (valuationOf q) (1277)) (literal (valuationOf q) (1285)) (countLit q [-25, -29, -30]) (countLit q [-31, -32, -35]) (count1285 q) 1 (meaning1277 q) (meaning1285 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1285 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1286 = true := by
  have hs : count1285 q = (countLit q [-25, -29, -30]) + (countLit q [-31, -32, -35]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30]) (l₂ := [-31, -32, -35])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1286)) (countLit q [-25, -29, -30]) (countLit q [-31, -32, -35]) (count1285 q) 1 1 (meaning1277 q) (meaning1282 q) (meaning1286 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1282 = false ∨ valuation q 1286 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1287 = true := by
  have hs : count1285 q = (countLit q [-25, -29, -30]) + (countLit q [-31, -32, -35]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30]) (l₂ := [-31, -32, -35])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1287)) (countLit q [-25, -29, -30]) (countLit q [-31, -32, -35]) (count1285 q) 1 2 (meaning1277 q) (meaning1283 q) (meaning1287 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1283 = false ∨ valuation q 1287 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1286 = true := by
  have hs : count1285 q = (countLit q [-25, -29, -30]) + (countLit q [-31, -32, -35]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30]) (l₂ := [-31, -32, -35])
  have hm := merge_left (literal (valuationOf q) (1278)) (literal (valuationOf q) (1286)) (countLit q [-25, -29, -30]) (countLit q [-31, -32, -35]) (count1285 q) 2 (meaning1278 q) (meaning1286 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1286 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1287 = true := by
  have hs : count1285 q = (countLit q [-25, -29, -30]) + (countLit q [-31, -32, -35]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30]) (l₂ := [-31, -32, -35])
  have hm := merge_two (literal (valuationOf q) (1278)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1287)) (countLit q [-25, -29, -30]) (countLit q [-31, -32, -35]) (count1285 q) 2 1 (meaning1278 q) (meaning1282 q) (meaning1287 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1282 = false ∨ valuation q 1287 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1288 = true := by
  have hs : count1285 q = (countLit q [-25, -29, -30]) + (countLit q [-31, -32, -35]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30]) (l₂ := [-31, -32, -35])
  have hm := merge_two (literal (valuationOf q) (1278)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1288)) (countLit q [-25, -29, -30]) (countLit q [-31, -32, -35]) (count1285 q) 2 2 (meaning1278 q) (meaning1283 q) (meaning1288 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1283 = false ∨ valuation q 1288 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1291)) (countLit q [-41]) (countLit q [-42]) (count1291 q) 1 (meaningNeg42 q) (meaning1291 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1291 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1291)) (countLit q [-41]) (countLit q [-42]) (count1291 q) 1 (meaningNeg41 q) (meaning1291 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1291 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1292 = true := by
  have hs : count1291 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1292)) (countLit q [-41]) (countLit q [-42]) (count1291 q) 1 1 (meaningNeg41 q) (meaningNeg42 q) (meaning1292 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 42 = true ∨ valuation q 1292 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-38]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -42])
  have hm := merge_right (literal (valuationOf q) (1291)) (literal (valuationOf q) (1293)) (countLit q [-38]) (countLit q [-41, -42]) (count1293 q) 1 (meaning1291 q) (meaning1293 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1293 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-38]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -42])
  have hm := merge_right (literal (valuationOf q) (1292)) (literal (valuationOf q) (1294)) (countLit q [-38]) (countLit q [-41, -42]) (count1293 q) 2 (meaning1292 q) (meaning1294 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1294 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-38]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -42])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1293)) (countLit q [-38]) (countLit q [-41, -42]) (count1293 q) 1 (meaningNeg38 q) (meaning1293 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1293 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1291 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-38]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -42])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (1291)) (literal (valuationOf q) (1294)) (countLit q [-38]) (countLit q [-41, -42]) (count1293 q) 1 1 (meaningNeg38 q) (meaning1291 q) (meaning1294 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1291 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1291 = false ∨ valuation q 1294 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1292 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-38]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -42])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (1292)) (literal (valuationOf q) (1295)) (countLit q [-38]) (countLit q [-41, -42]) (count1293 q) 1 2 (meaningNeg38 q) (meaning1292 q) (meaning1295 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1292 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1292 = false ∨ valuation q 1295 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1296)) (countLit q [-43]) (countLit q [-45]) (count1296 q) 1 (meaningNeg45 q) (meaning1296 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1296 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1296)) (countLit q [-43]) (countLit q [-45]) (count1296 q) 1 (meaningNeg43 q) (meaning1296 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1296 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1297 = true := by
  have hs : count1296 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1297)) (countLit q [-43]) (countLit q [-45]) (count1296 q) 1 1 (meaningNeg43 q) (meaningNeg45 q) (meaning1297 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 1297 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1298 = true := by
  have hs : count1298 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1298)) (countLit q [-47]) (countLit q [-50]) (count1298 q) 1 (meaningNeg50 q) (meaning1298 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1298 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1298 = true := by
  have hs : count1298 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1298)) (countLit q [-47]) (countLit q [-50]) (count1298 q) 1 (meaningNeg47 q) (meaning1298 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1298 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1300 = true := by
  have hs : count1300 q = (countLit q [-43, -45]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -45]) (l₂ := [-47, -50])
  have hm := merge_right (literal (valuationOf q) (1298)) (literal (valuationOf q) (1300)) (countLit q [-43, -45]) (countLit q [-47, -50]) (count1300 q) 1 (meaning1298 q) (meaning1300 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1300 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1300 = true := by
  have hs : count1300 q = (countLit q [-43, -45]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -45]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1296)) (literal (valuationOf q) (1300)) (countLit q [-43, -45]) (countLit q [-47, -50]) (count1300 q) 1 (meaning1296 q) (meaning1300 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1300 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1301 = true := by
  have hs : count1300 q = (countLit q [-43, -45]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -45]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1296)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1301)) (countLit q [-43, -45]) (countLit q [-47, -50]) (count1300 q) 1 1 (meaning1296 q) (meaning1298 q) (meaning1301 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1298 = false ∨ valuation q 1301 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1297 = false ∨ valuationOf q 1301 = true := by
  have hs : count1300 q = (countLit q [-43, -45]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -45]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1297)) (literal (valuationOf q) (1301)) (countLit q [-43, -45]) (countLit q [-47, -50]) (count1300 q) 2 (meaning1297 q) (meaning1301 q) hs
  change valuationOf q 1297 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1297 = false ∨ valuation q 1301 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E145.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112145
