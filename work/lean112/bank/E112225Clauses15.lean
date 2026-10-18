import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 1 2 (meaning1391 q) (meaning1411 q) (meaning1419 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1411 = false ∨ valuation q 1419 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1420)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 1 3 (meaning1391 q) (meaning1412 q) (meaning1420 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1412 = false ∨ valuation q 1420 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1421)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 1 4 (meaning1391 q) (meaning1413 q) (meaning1421 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1413 = false ∨ valuation q 1421 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1419)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 2 1 (meaning1392 q) (meaning1410 q) (meaning1419 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1410 = false ∨ valuation q 1419 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1420)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 2 2 (meaning1392 q) (meaning1411 q) (meaning1420 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1411 = false ∨ valuation q 1420 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1421)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 2 3 (meaning1392 q) (meaning1412 q) (meaning1421 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1412 = false ∨ valuation q 1421 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1422 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1422)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 2 4 (meaning1392 q) (meaning1413 q) (meaning1422 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1413 = false ∨ valuation q 1422 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1420)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 3 1 (meaning1393 q) (meaning1410 q) (meaning1420 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1410 = false ∨ valuation q 1420 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1421)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 3 2 (meaning1393 q) (meaning1411 q) (meaning1421 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1411 = false ∨ valuation q 1421 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1422 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1422)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 3 3 (meaning1393 q) (meaning1412 q) (meaning1422 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1412 = false ∨ valuation q 1422 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1423 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1423)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 3 4 (meaning1393 q) (meaning1413 q) (meaning1423 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1413 = false ∨ valuation q 1423 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1430)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 4 (meaning1420 q) (meaning1430 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1430 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1431)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 5 (meaning1421 q) (meaning1431 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1431 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1432)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 6 (meaning1422 q) (meaning1432 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1432 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1433)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 7 (meaning1423 q) (meaning1433 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1433 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1429)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 1 2 (meaning1371 q) (meaning1418 q) (meaning1429 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1418 = false ∨ valuation q 1429 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1430)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 1 3 (meaning1371 q) (meaning1419 q) (meaning1430 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1419 = false ∨ valuation q 1430 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1431)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 1 4 (meaning1371 q) (meaning1420 q) (meaning1431 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1420 = false ∨ valuation q 1431 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1432)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 1 5 (meaning1371 q) (meaning1421 q) (meaning1432 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1421 = false ∨ valuation q 1432 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1433)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 1 6 (meaning1371 q) (meaning1422 q) (meaning1433 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1422 = false ∨ valuation q 1433 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1431)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 2 3 (meaning1372 q) (meaning1419 q) (meaning1431 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1419 = false ∨ valuation q 1431 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1432)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 2 4 (meaning1372 q) (meaning1420 q) (meaning1432 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1420 = false ∨ valuation q 1432 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1433)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 2 5 (meaning1372 q) (meaning1421 q) (meaning1433 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1421 = false ∨ valuation q 1433 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1431)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 3 2 (meaning1373 q) (meaning1418 q) (meaning1431 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1418 = false ∨ valuation q 1431 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1432)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 3 3 (meaning1373 q) (meaning1419 q) (meaning1432 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1419 = false ∨ valuation q 1432 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1433)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 3 4 (meaning1373 q) (meaning1420 q) (meaning1433 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1420 = false ∨ valuation q 1433 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) + (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (l₂ := [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1432)) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76]) (countLit q [-77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1427 q) 4 2 (meaning1374 q) (meaning1418 q) (meaning1432 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1418 = false ∨ valuation q 1432 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) + (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (l₂ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1437 q) 3 7 (meaning1331 q) (meaning1433 q) (meaning1446 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1433 = false ∨ valuation q 1446 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) + (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (l₂ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1437 q) 4 6 (meaning1332 q) (meaning1432 q) (meaning1446 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1432 = false ∨ valuation q 1446 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) + (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (l₂ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1437 q) 5 5 (meaning1333 q) (meaning1431 q) (meaning1446 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1431 = false ∨ valuation q 1446 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) + (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (l₂ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1437 q) 6 4 (meaning1334 q) (meaning1430 q) (meaning1446 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1430 = false ∨ valuation q 1446 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1446 = true := by
  have hs : count1437 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) + (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (l₂ := [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24, -27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (countLit q [-52, -55, -58, -59, -61, -64, -66, -68, -70, -73, -74, -76, -77, -81, -83, -85, -87, -88, -91, -92, -96, -98, -99, -101, -103]) (count1437 q) 7 3 (meaning1335 q) (meaning1429 q) (meaning1446 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1429 = false ∨ valuation q 1446 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E225.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112225
