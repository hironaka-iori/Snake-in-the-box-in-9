import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1464 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1464)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 2 1 (meaning1452 q) (meaning1458 q) (meaning1464 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1458 = false ∨ valuation q 1464 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1465 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1459)) (literal (valuationOf q) (1465)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 2 2 (meaning1452 q) (meaning1459 q) (meaning1465 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1459 = false ∨ valuation q 1465 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1464 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1453)) (literal (valuationOf q) (1464)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 3 (meaning1453 q) (meaning1464 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1464 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1465 = true := by
  have hs : count1462 q = (countLit q [-81, -82, -85]) + (countLit q [-87, -89, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85]) (l₂ := [-87, -89, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1465)) (countLit q [-81, -82, -85]) (countLit q [-87, -89, -92, -93]) (count1462 q) 3 1 (meaning1453 q) (meaning1458 q) (meaning1465 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1458 = false ∨ valuation q 1465 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1469)) (countLit q [-97]) (countLit q [-99]) (count1469 q) 1 (meaningNeg99 q) (meaning1469 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1469 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1469)) (countLit q [-97]) (countLit q [-99]) (count1469 q) 1 (meaningNeg97 q) (meaning1469 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1469 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1470 = true := by
  have hs : count1469 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1470)) (countLit q [-97]) (countLit q [-99]) (count1469 q) 1 1 (meaningNeg97 q) (meaningNeg99 q) (meaning1470 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 99 = true ∨ valuation q 1470 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-96]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97, -99])
  have hm := merge_right (literal (valuationOf q) (1469)) (literal (valuationOf q) (1471)) (countLit q [-96]) (countLit q [-97, -99]) (count1471 q) 1 (meaning1469 q) (meaning1471 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1471 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1472 = true := by
  have hs : count1471 q = (countLit q [-96]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97, -99])
  have hm := merge_right (literal (valuationOf q) (1470)) (literal (valuationOf q) (1472)) (countLit q [-96]) (countLit q [-97, -99]) (count1471 q) 2 (meaning1470 q) (meaning1472 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1472 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-96]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97, -99])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1471)) (countLit q [-96]) (countLit q [-97, -99]) (count1471 q) 1 (meaningNeg96 q) (meaning1471 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1471 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1469 = false ∨ valuationOf q 1472 = true := by
  have hs : count1471 q = (countLit q [-96]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97, -99])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1472)) (countLit q [-96]) (countLit q [-97, -99]) (count1471 q) 1 1 (meaningNeg96 q) (meaning1469 q) (meaning1472 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1469 = false ∨ valuation q 1472 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1470 = false ∨ valuationOf q 1473 = true := by
  have hs : count1471 q = (countLit q [-96]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97, -99])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1473)) (countLit q [-96]) (countLit q [-97, -99]) (count1471 q) 1 2 (meaningNeg96 q) (meaning1470 q) (meaning1473 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1470 = false ∨ valuation q 1473 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1474)) (countLit q [-102]) (countLit q [-103]) (count1474 q) 1 (meaningNeg103 q) (meaning1474 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1474 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1474)) (countLit q [-102]) (countLit q [-103]) (count1474 q) 1 (meaningNeg102 q) (meaning1474 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1474 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1475)) (countLit q [-102]) (countLit q [-103]) (count1474 q) 1 1 (meaningNeg102 q) (meaningNeg103 q) (meaning1475 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 1475 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1476)) (countLit q [-105]) (countLit q [-108]) (count1476 q) 1 (meaningNeg108 q) (meaning1476 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1476 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1476)) (countLit q [-105]) (countLit q [-108]) (count1476 q) 1 (meaningNeg105 q) (meaning1476 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1476 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1477)) (countLit q [-105]) (countLit q [-108]) (count1476 q) 1 1 (meaningNeg105 q) (meaningNeg108 q) (meaning1477 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 108 = true ∨ valuation q 1477 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-102, -103]) + (countLit q [-105, -108]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-105, -108])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1478)) (countLit q [-102, -103]) (countLit q [-105, -108]) (count1478 q) 1 (meaning1476 q) (meaning1478 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1478 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-102, -103]) + (countLit q [-105, -108]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-105, -108])
  have hm := merge_left (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-102, -103]) (countLit q [-105, -108]) (count1478 q) 1 (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-102, -103]) + (countLit q [-105, -108]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-105, -108])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1479)) (countLit q [-102, -103]) (countLit q [-105, -108]) (count1478 q) 1 1 (meaning1474 q) (meaning1476 q) (meaning1479 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1476 = false ∨ valuation q 1479 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-102, -103]) + (countLit q [-105, -108]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-105, -108])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1480)) (countLit q [-102, -103]) (countLit q [-105, -108]) (count1478 q) 1 2 (meaning1474 q) (meaning1477 q) (meaning1480 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1477 = false ∨ valuation q 1480 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-102, -103]) + (countLit q [-105, -108]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-105, -108])
  have hm := merge_left (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-102, -103]) (countLit q [-105, -108]) (count1478 q) 2 (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1479 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-102, -103]) + (countLit q [-105, -108]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-105, -108])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-102, -103]) (countLit q [-105, -108]) (count1478 q) 2 1 (meaning1475 q) (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1476 = false ∨ valuation q 1480 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 1 (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1482 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 2 (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1483 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 3 (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1484 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1482)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 1 (meaning1471 q) (meaning1482 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1482 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1483)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 1 1 (meaning1471 q) (meaning1478 q) (meaning1483 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1478 = false ∨ valuation q 1483 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1484 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1484)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 1 2 (meaning1471 q) (meaning1479 q) (meaning1484 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1479 = false ∨ valuation q 1484 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1485 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1485)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 1 3 (meaning1471 q) (meaning1480 q) (meaning1485 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1480 = false ∨ valuation q 1485 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -103, -105, -108]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -103, -105, -108])
  have hm := merge_left (literal (valuationOf q) (1472)) (literal (valuationOf q) (1483)) (countLit q [-96, -97, -99]) (countLit q [-102, -103, -105, -108]) (count1482 q) 2 (meaning1472 q) (meaning1483 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1483 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E190.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112190
