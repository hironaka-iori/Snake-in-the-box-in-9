import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1440)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 2 (meaning1436 q) (meaning1440 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1440 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_left (literal (valuationOf q) (1427)) (literal (valuationOf q) (1439)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 1 (meaning1427 q) (meaning1439 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1439 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1440)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 1 1 (meaning1427 q) (meaning1435 q) (meaning1440 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1435 = false ∨ valuation q 1440 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1441 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1441)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 1 2 (meaning1427 q) (meaning1436 q) (meaning1441 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1436 = false ∨ valuation q 1441 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1442 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1442)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 1 3 (meaning1427 q) (meaning1437 q) (meaning1442 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1437 = false ∨ valuation q 1442 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_left (literal (valuationOf q) (1428)) (literal (valuationOf q) (1440)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 2 (meaning1428 q) (meaning1440 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1440 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1441 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1441)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 2 1 (meaning1428 q) (meaning1435 q) (meaning1441 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1435 = false ∨ valuation q 1441 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1442 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1442)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 2 2 (meaning1428 q) (meaning1436 q) (meaning1442 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1436 = false ∨ valuation q 1442 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1441 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_left (literal (valuationOf q) (1429)) (literal (valuationOf q) (1441)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 3 (meaning1429 q) (meaning1441 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1441 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1442 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1442)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 3 1 (meaning1429 q) (meaning1435 q) (meaning1442 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1435 = false ∨ valuation q 1442 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1450 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1450)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 1 3 (meaning1416 q) (meaning1441 q) (meaning1450 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1441 = false ∨ valuation q 1450 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1450 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1450)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 2 2 (meaning1417 q) (meaning1440 q) (meaning1450 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1440 = false ∨ valuation q 1450 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1451 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1451)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 2 3 (meaning1417 q) (meaning1441 q) (meaning1451 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1441 = false ∨ valuation q 1451 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1452 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1452)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 2 4 (meaning1417 q) (meaning1442 q) (meaning1452 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1442 = false ∨ valuation q 1452 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1450 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1450)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 3 1 (meaning1418 q) (meaning1439 q) (meaning1450 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1439 = false ∨ valuation q 1450 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1451 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1451)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 3 2 (meaning1418 q) (meaning1440 q) (meaning1451 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1440 = false ∨ valuation q 1451 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1452 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1452)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 3 3 (meaning1418 q) (meaning1441 q) (meaning1452 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1441 = false ∨ valuation q 1452 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1453 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1453)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 3 4 (meaning1418 q) (meaning1442 q) (meaning1453 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1442 = false ∨ valuation q 1453 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1450 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_left (literal (valuationOf q) (1419)) (literal (valuationOf q) (1450)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 4 (meaning1419 q) (meaning1450 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1450 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1451 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1451)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 4 1 (meaning1419 q) (meaning1439 q) (meaning1451 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1439 = false ∨ valuation q 1451 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1452 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1452)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 4 2 (meaning1419 q) (meaning1440 q) (meaning1452 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1440 = false ∨ valuation q 1452 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1453 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1453)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 4 3 (meaning1419 q) (meaning1441 q) (meaning1453 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1441 = false ∨ valuation q 1453 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1454 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1454)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 4 4 (meaning1419 q) (meaning1442 q) (meaning1454 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1442 = false ∨ valuation q 1454 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1451 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_left (literal (valuationOf q) (1420)) (literal (valuationOf q) (1451)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 5 (meaning1420 q) (meaning1451 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1451 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1452 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1452)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 5 1 (meaning1420 q) (meaning1439 q) (meaning1452 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1439 = false ∨ valuation q 1452 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1453 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1453)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 5 2 (meaning1420 q) (meaning1440 q) (meaning1453 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1440 = false ∨ valuation q 1453 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1454 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1454)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 5 3 (meaning1420 q) (meaning1441 q) (meaning1454 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1441 = false ∨ valuation q 1454 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1455 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1455)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 5 4 (meaning1420 q) (meaning1442 q) (meaning1455 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1442 = false ∨ valuation q 1455 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1452 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_left (literal (valuationOf q) (1421)) (literal (valuationOf q) (1452)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 6 (meaning1421 q) (meaning1452 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1452 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1453 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1453)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 6 1 (meaning1421 q) (meaning1439 q) (meaning1453 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1439 = false ∨ valuation q 1453 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1454 = true := by
  have hs : count1447 q = (countLit q [-26, -30, -31, -33, -35, -37, -39]) + (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31, -33, -35, -37, -39]) (l₂ := [-40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1454)) (countLit q [-26, -30, -31, -33, -35, -37, -39]) (countLit q [-40, -41, -43, -46, -48, -51, -53, -55]) (count1447 q) 6 2 (meaning1421 q) (meaning1440 q) (meaning1454 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1440 = false ∨ valuation q 1454 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1471 = true := by
  have hs : count1462 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) + (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (l₂ := [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1471)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]) (countLit q [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (count1462 q) 5 5 (meaning1393 q) (meaning1451 q) (meaning1471 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1451 = false ∨ valuation q 1471 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E146.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112146
