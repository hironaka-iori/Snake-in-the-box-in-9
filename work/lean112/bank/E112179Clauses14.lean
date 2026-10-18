import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-29]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1283)) (countLit q [-29]) (countLit q [-32]) (count1283 q) 1 (meaningNeg29 q) (meaning1283 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1283 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-26]) + (countLit q [-29, -32]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29, -32])
  have hm := merge_right (literal (valuationOf q) (1283)) (literal (valuationOf q) (1285)) (countLit q [-26]) (countLit q [-29, -32]) (count1285 q) 1 (meaning1283 q) (meaning1285 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1285 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-26]) + (countLit q [-29, -32]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29, -32])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1285)) (countLit q [-26]) (countLit q [-29, -32]) (count1285 q) 1 (meaningNeg26 q) (meaning1285 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1285 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true := by
  have hs : count1285 q = (countLit q [-26]) + (countLit q [-29, -32]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29, -32])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1286)) (countLit q [-26]) (countLit q [-29, -32]) (count1285 q) 1 1 (meaningNeg26 q) (meaning1283 q) (meaning1286 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1283 = false ∨ valuation q 1286 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1288)) (countLit q [-35]) (countLit q [-37]) (count1288 q) 1 (meaningNeg37 q) (meaning1288 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1288 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1288)) (countLit q [-35]) (countLit q [-37]) (count1288 q) 1 (meaningNeg35 q) (meaning1288 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1288 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1289)) (countLit q [-35]) (countLit q [-37]) (count1288 q) 1 1 (meaningNeg35 q) (meaningNeg37 q) (meaning1289 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 37 = true ∨ valuation q 1289 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-34]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1288)) (literal (valuationOf q) (1290)) (countLit q [-34]) (countLit q [-35, -37]) (count1290 q) 1 (meaning1288 q) (meaning1290 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1290 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1291 = true := by
  have hs : count1290 q = (countLit q [-34]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1289)) (literal (valuationOf q) (1291)) (countLit q [-34]) (countLit q [-35, -37]) (count1290 q) 2 (meaning1289 q) (meaning1291 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1291 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-34]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35, -37])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1290)) (countLit q [-34]) (countLit q [-35, -37]) (count1290 q) 1 (meaningNeg34 q) (meaning1290 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1290 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1288 = false ∨ valuationOf q 1291 = true := by
  have hs : count1290 q = (countLit q [-34]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35, -37])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1291)) (countLit q [-34]) (countLit q [-35, -37]) (count1290 q) 1 1 (meaningNeg34 q) (meaning1288 q) (meaning1291 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1288 = false ∨ valuation q 1291 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-26, -29, -32]) + (countLit q [-34, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32]) (l₂ := [-34, -35, -37])
  have hm := merge_right (literal (valuationOf q) (1290)) (literal (valuationOf q) (1293)) (countLit q [-26, -29, -32]) (countLit q [-34, -35, -37]) (count1293 q) 1 (meaning1290 q) (meaning1293 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1293 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-26, -29, -32]) + (countLit q [-34, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32]) (l₂ := [-34, -35, -37])
  have hm := merge_right (literal (valuationOf q) (1291)) (literal (valuationOf q) (1294)) (countLit q [-26, -29, -32]) (countLit q [-34, -35, -37]) (count1293 q) 2 (meaning1291 q) (meaning1294 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1294 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-26, -29, -32]) + (countLit q [-34, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32]) (l₂ := [-34, -35, -37])
  have hm := merge_left (literal (valuationOf q) (1285)) (literal (valuationOf q) (1293)) (countLit q [-26, -29, -32]) (countLit q [-34, -35, -37]) (count1293 q) 1 (meaning1285 q) (meaning1293 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1293 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-26, -29, -32]) + (countLit q [-34, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32]) (l₂ := [-34, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1285)) (literal (valuationOf q) (1290)) (literal (valuationOf q) (1294)) (countLit q [-26, -29, -32]) (countLit q [-34, -35, -37]) (count1293 q) 1 1 (meaning1285 q) (meaning1290 q) (meaning1294 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1290 = false ∨ valuation q 1294 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1291 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-26, -29, -32]) + (countLit q [-34, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32]) (l₂ := [-34, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1285)) (literal (valuationOf q) (1291)) (literal (valuationOf q) (1295)) (countLit q [-26, -29, -32]) (countLit q [-34, -35, -37]) (count1293 q) 1 2 (meaning1285 q) (meaning1291 q) (meaning1295 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1291 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1291 = false ∨ valuation q 1295 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-26, -29, -32]) + (countLit q [-34, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32]) (l₂ := [-34, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1286)) (literal (valuationOf q) (1290)) (literal (valuationOf q) (1295)) (countLit q [-26, -29, -32]) (countLit q [-34, -35, -37]) (count1293 q) 2 1 (meaning1286 q) (meaning1290 q) (meaning1295 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1290 = false ∨ valuation q 1295 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (1299)) (countLit q [-42]) (countLit q [-43]) (count1299 q) 1 (meaningNeg43 q) (meaning1299 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1299 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-42]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1299)) (countLit q [-42]) (countLit q [-43]) (count1299 q) 1 (meaningNeg42 q) (meaning1299 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1299 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -43])
  have hm := merge_right (literal (valuationOf q) (1299)) (literal (valuationOf q) (1301)) (countLit q [-41]) (countLit q [-42, -43]) (count1301 q) 1 (meaning1299 q) (meaning1301 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1301 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-41]) + (countLit q [-42, -43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -43])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1301)) (countLit q [-41]) (countLit q [-42, -43]) (count1301 q) 1 (meaningNeg41 q) (meaning1301 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1301 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-44]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1304)) (countLit q [-44]) (countLit q [-48]) (count1304 q) 1 (meaningNeg48 q) (meaning1304 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1304 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-44]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1304)) (countLit q [-44]) (countLit q [-48]) (count1304 q) 1 (meaningNeg44 q) (meaning1304 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1304 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1306)) (countLit q [-49]) (countLit q [-52]) (count1306 q) 1 (meaningNeg49 q) (meaning1306 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1306 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-44, -48]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-49, -52])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1308)) (countLit q [-44, -48]) (countLit q [-49, -52]) (count1308 q) 1 (meaning1306 q) (meaning1308 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1308 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-44, -48]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-49, -52])
  have hm := merge_left (literal (valuationOf q) (1304)) (literal (valuationOf q) (1308)) (countLit q [-44, -48]) (countLit q [-49, -52]) (count1308 q) 1 (meaning1304 q) (meaning1308 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1308 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true := by
  have hs : count1308 q = (countLit q [-44, -48]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-49, -52])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1309)) (countLit q [-44, -48]) (countLit q [-49, -52]) (count1308 q) 1 1 (meaning1304 q) (meaning1306 q) (meaning1309 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1306 = false ∨ valuation q 1309 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-41, -42, -43]) + (countLit q [-44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -43]) (l₂ := [-44, -48, -49, -52])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1312)) (countLit q [-41, -42, -43]) (countLit q [-44, -48, -49, -52]) (count1312 q) 1 (meaning1308 q) (meaning1312 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1312 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1313 = true := by
  have hs : count1312 q = (countLit q [-41, -42, -43]) + (countLit q [-44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -43]) (l₂ := [-44, -48, -49, -52])
  have hm := merge_right (literal (valuationOf q) (1309)) (literal (valuationOf q) (1313)) (countLit q [-41, -42, -43]) (countLit q [-44, -48, -49, -52]) (count1312 q) 2 (meaning1309 q) (meaning1313 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1313 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-41, -42, -43]) + (countLit q [-44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -43]) (l₂ := [-44, -48, -49, -52])
  have hm := merge_left (literal (valuationOf q) (1301)) (literal (valuationOf q) (1312)) (countLit q [-41, -42, -43]) (countLit q [-44, -48, -49, -52]) (count1312 q) 1 (meaning1301 q) (meaning1312 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1312 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1313 = true := by
  have hs : count1312 q = (countLit q [-41, -42, -43]) + (countLit q [-44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -43]) (l₂ := [-44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1313)) (countLit q [-41, -42, -43]) (countLit q [-44, -48, -49, -52]) (count1312 q) 1 1 (meaning1301 q) (meaning1308 q) (meaning1313 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1308 = false ∨ valuation q 1313 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-26, -29, -32, -34, -35, -37]) + (countLit q [-41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32, -34, -35, -37]) (l₂ := [-41, -42, -43, -44, -48, -49, -52])
  have hm := merge_right (literal (valuationOf q) (1312)) (literal (valuationOf q) (1319)) (countLit q [-26, -29, -32, -34, -35, -37]) (countLit q [-41, -42, -43, -44, -48, -49, -52]) (count1319 q) 1 (meaning1312 q) (meaning1319 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1319 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E179.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112179
