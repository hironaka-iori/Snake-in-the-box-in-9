import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-98, -99]) + (countLit q [-103, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-103, -106])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1443)) (countLit q [-98, -99]) (countLit q [-103, -106]) (count1442 q) 1 1 (meaning1438 q) (meaning1440 q) (meaning1443 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1440 = false ∨ valuation q 1443 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-98, -99]) + (countLit q [-103, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-103, -106])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1444)) (countLit q [-98, -99]) (countLit q [-103, -106]) (count1442 q) 1 2 (meaning1438 q) (meaning1441 q) (meaning1444 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1441 = false ∨ valuation q 1444 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-98, -99]) + (countLit q [-103, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-103, -106])
  have hm := merge_left (literal (valuationOf q) (1439)) (literal (valuationOf q) (1443)) (countLit q [-98, -99]) (countLit q [-103, -106]) (count1442 q) 2 (meaning1439 q) (meaning1443 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1443 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-98, -99]) + (countLit q [-103, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-103, -106])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1444)) (countLit q [-98, -99]) (countLit q [-103, -106]) (count1442 q) 2 1 (meaning1439 q) (meaning1440 q) (meaning1444 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1440 = false ∨ valuation q 1444 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-92, -94, -96]) + (countLit q [-98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96]) (l₂ := [-98, -99, -103, -106])
  have hm := merge_left (literal (valuationOf q) (1435)) (literal (valuationOf q) (1446)) (countLit q [-92, -94, -96]) (countLit q [-98, -99, -103, -106]) (count1446 q) 1 (meaning1435 q) (meaning1446 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1446 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-92, -94, -96]) + (countLit q [-98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96]) (l₂ := [-98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1447)) (countLit q [-92, -94, -96]) (countLit q [-98, -99, -103, -106]) (count1446 q) 1 1 (meaning1435 q) (meaning1442 q) (meaning1447 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1442 = false ∨ valuation q 1447 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1448 = true := by
  have hs : count1446 q = (countLit q [-92, -94, -96]) + (countLit q [-98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96]) (l₂ := [-98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (countLit q [-92, -94, -96]) (countLit q [-98, -99, -103, -106]) (count1446 q) 1 2 (meaning1435 q) (meaning1443 q) (meaning1448 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1443 = false ∨ valuation q 1448 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1449 = true := by
  have hs : count1446 q = (countLit q [-92, -94, -96]) + (countLit q [-98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96]) (l₂ := [-98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1449)) (countLit q [-92, -94, -96]) (countLit q [-98, -99, -103, -106]) (count1446 q) 1 3 (meaning1435 q) (meaning1444 q) (meaning1449 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1444 = false ∨ valuation q 1449 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-92, -94, -96]) + (countLit q [-98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96]) (l₂ := [-98, -99, -103, -106])
  have hm := merge_left (literal (valuationOf q) (1436)) (literal (valuationOf q) (1447)) (countLit q [-92, -94, -96]) (countLit q [-98, -99, -103, -106]) (count1446 q) 2 (meaning1436 q) (meaning1447 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1447 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1448 = true := by
  have hs : count1446 q = (countLit q [-92, -94, -96]) + (countLit q [-98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96]) (l₂ := [-98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1448)) (countLit q [-92, -94, -96]) (countLit q [-98, -99, -103, -106]) (count1446 q) 2 1 (meaning1436 q) (meaning1442 q) (meaning1448 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1442 = false ∨ valuation q 1448 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1449 = true := by
  have hs : count1446 q = (countLit q [-92, -94, -96]) + (countLit q [-98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96]) (l₂ := [-98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1449)) (countLit q [-92, -94, -96]) (countLit q [-98, -99, -103, -106]) (count1446 q) 2 2 (meaning1436 q) (meaning1443 q) (meaning1449 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1443 = false ∨ valuation q 1449 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1449 = true := by
  have hs : count1446 q = (countLit q [-92, -94, -96]) + (countLit q [-98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -94, -96]) (l₂ := [-98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1449)) (countLit q [-92, -94, -96]) (countLit q [-98, -99, -103, -106]) (count1446 q) 3 1 (meaning1437 q) (meaning1442 q) (meaning1449 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1442 = false ∨ valuation q 1449 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1455 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1455)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 1 2 (meaning1427 q) (meaning1447 q) (meaning1455 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1447 = false ∨ valuation q 1455 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1456 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1456)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 1 3 (meaning1427 q) (meaning1448 q) (meaning1456 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1448 = false ∨ valuation q 1456 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1457 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1457)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 1 4 (meaning1427 q) (meaning1449 q) (meaning1457 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1449 = false ∨ valuation q 1457 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1455)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 2 1 (meaning1428 q) (meaning1446 q) (meaning1455 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1446 = false ∨ valuation q 1455 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1456)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 2 2 (meaning1428 q) (meaning1447 q) (meaning1456 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1447 = false ∨ valuation q 1456 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1457 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1457)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 2 3 (meaning1428 q) (meaning1448 q) (meaning1457 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1448 = false ∨ valuation q 1457 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1458 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1458)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 2 4 (meaning1428 q) (meaning1449 q) (meaning1458 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1449 = false ∨ valuation q 1458 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1456 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1456)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 3 1 (meaning1429 q) (meaning1446 q) (meaning1456 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1446 = false ∨ valuation q 1456 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1457 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1457)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 3 2 (meaning1429 q) (meaning1447 q) (meaning1457 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1447 = false ∨ valuation q 1457 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1458 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1458)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 3 3 (meaning1429 q) (meaning1448 q) (meaning1458 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1448 = false ∨ valuation q 1458 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1459 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1459)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 3 4 (meaning1429 q) (meaning1449 q) (meaning1459 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1449 = false ∨ valuation q 1459 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1457 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1457)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 4 1 (meaning1430 q) (meaning1446 q) (meaning1457 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1446 = false ∨ valuation q 1457 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1458 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1458)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 4 2 (meaning1430 q) (meaning1447 q) (meaning1458 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1447 = false ∨ valuation q 1458 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1459 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1459)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 4 3 (meaning1430 q) (meaning1448 q) (meaning1459 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1448 = false ∨ valuation q 1459 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1459 = true := by
  have hs : count1453 q = (countLit q [-81, -82, -84, -85, -87, -91]) + (countLit q [-92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -85, -87, -91]) (l₂ := [-92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1459)) (countLit q [-81, -82, -84, -85, -87, -91]) (countLit q [-92, -94, -96, -98, -99, -103, -106]) (count1453 q) 5 2 (meaning1431 q) (meaning1447 q) (meaning1459 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1447 = false ∨ valuation q 1459 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_right (literal (valuationOf q) (1458)) (literal (valuationOf q) (1470)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 6 (meaning1458 q) (meaning1470 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1470 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_right (literal (valuationOf q) (1459)) (literal (valuationOf q) (1471)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 7 (meaning1459 q) (meaning1471 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1471 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1469)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 1 4 (meaning1405 q) (meaning1456 q) (meaning1469 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1456 = false ∨ valuation q 1469 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1470)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 1 5 (meaning1405 q) (meaning1457 q) (meaning1470 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1457 = false ∨ valuation q 1470 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) + (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (l₂ := [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1471)) (countLit q [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]) (countLit q [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]) (count1465 q) 1 6 (meaning1405 q) (meaning1458 q) (meaning1471 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1458 = false ∨ valuation q 1471 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E150.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112150
