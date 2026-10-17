import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1490)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 2 1 (meaning1478 q) (meaning1484 q) (meaning1490 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1484 = false ∨ valuation q 1490 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 3 (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1490 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1491)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 3 1 (meaning1479 q) (meaning1484 q) (meaning1491 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1484 = false ∨ valuation q 1491 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1497 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1490)) (literal (valuationOf q) (1497)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 3 (meaning1490 q) (meaning1497 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1497 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1496 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1496)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 1 1 (meaning1468 q) (meaning1488 q) (meaning1496 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1488 = false ∨ valuation q 1496 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1497 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1497)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 1 2 (meaning1468 q) (meaning1489 q) (meaning1497 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1489 = false ∨ valuation q 1497 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1498)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 1 3 (meaning1468 q) (meaning1490 q) (meaning1498 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1490 = false ∨ valuation q 1498 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1499)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 1 4 (meaning1468 q) (meaning1491 q) (meaning1499 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1491 = false ∨ valuation q 1499 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1497 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1497)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 2 1 (meaning1469 q) (meaning1488 q) (meaning1497 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1488 = false ∨ valuation q 1497 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1498)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 2 2 (meaning1469 q) (meaning1489 q) (meaning1498 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1489 = false ∨ valuation q 1498 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1499)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 2 3 (meaning1469 q) (meaning1490 q) (meaning1499 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1490 = false ∨ valuation q 1499 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1498)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 3 1 (meaning1470 q) (meaning1488 q) (meaning1498 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1488 = false ∨ valuation q 1498 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1499)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 3 2 (meaning1470 q) (meaning1489 q) (meaning1499 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1489 = false ∨ valuation q 1499 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1500)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 3 3 (meaning1470 q) (meaning1490 q) (meaning1500 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1490 = false ∨ valuation q 1500 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1499)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 4 1 (meaning1471 q) (meaning1488 q) (meaning1499 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1488 = false ∨ valuation q 1499 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1500)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 4 2 (meaning1471 q) (meaning1489 q) (meaning1500 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1489 = false ∨ valuation q 1500 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1501 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1501)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 4 3 (meaning1471 q) (meaning1490 q) (meaning1501 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1490 = false ∨ valuation q 1501 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1500)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 5 1 (meaning1472 q) (meaning1488 q) (meaning1500 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1488 = false ∨ valuation q 1500 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1501 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1501)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 5 2 (meaning1472 q) (meaning1489 q) (meaning1501 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1489 = false ∨ valuation q 1501 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1502 = true := by
  have hs : count1495 q = (countLit q [-33, -34, -35, -37, -39, -42, -43]) + (countLit q [-46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35, -37, -39, -42, -43]) (l₂ := [-46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1502)) (countLit q [-33, -34, -35, -37, -39, -42, -43]) (countLit q [-46, -48, -49, -51, -52, -56, -57]) (count1495 q) 5 3 (meaning1472 q) (meaning1490 q) (meaning1502 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1490 = false ∨ valuation q 1502 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1513 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1513)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 1 4 (meaning1441 q) (meaning1498 q) (meaning1513 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1498 = false ∨ valuation q 1513 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1514)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 1 5 (meaning1441 q) (meaning1499 q) (meaning1514 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1499 = false ∨ valuation q 1514 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 1 6 (meaning1441 q) (meaning1500 q) (meaning1515 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1500 = false ∨ valuation q 1515 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 1 7 (meaning1441 q) (meaning1501 q) (meaning1516 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1501 = false ∨ valuation q 1516 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1513 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1513)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 2 3 (meaning1442 q) (meaning1497 q) (meaning1513 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1497 = false ∨ valuation q 1513 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1514)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 2 4 (meaning1442 q) (meaning1498 q) (meaning1514 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1498 = false ∨ valuation q 1514 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 2 5 (meaning1442 q) (meaning1499 q) (meaning1515 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1499 = false ∨ valuation q 1515 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 2 6 (meaning1442 q) (meaning1500 q) (meaning1516 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1500 = false ∨ valuation q 1516 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 2 7 (meaning1442 q) (meaning1501 q) (meaning1517 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1501 = false ∨ valuation q 1517 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 2 8 (meaning1442 q) (meaning1502 q) (meaning1518 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1502 = false ∨ valuation q 1518 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1514)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 3 3 (meaning1443 q) (meaning1497 q) (meaning1514 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1497 = false ∨ valuation q 1514 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) + (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (l₂ := [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30]) (countLit q [-33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (count1509 q) 3 4 (meaning1443 q) (meaning1498 q) (meaning1515 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1498 = false ∨ valuation q 1515 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E058.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112058
