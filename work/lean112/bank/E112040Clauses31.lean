import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (1470)) (literal (valuationOf q) (1474)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 2 (meaning1470 q) (meaning1474 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1474 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1475 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1475)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 2 1 (meaning1470 q) (meaning1471 q) (meaning1475 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1471 = false ∨ valuation q 1475 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 2 2 (meaning1470 q) (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1472 = false ∨ valuation q 1476 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1477 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1479 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1480 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1465)) (literal (valuationOf q) (1477)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 (meaning1465 q) (meaning1477 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1477 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1478)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 1 (meaning1465 q) (meaning1473 q) (meaning1478 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1473 = false ∨ valuation q 1478 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 2 (meaning1465 q) (meaning1474 q) (meaning1479 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1474 = false ∨ valuation q 1479 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1480)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 3 (meaning1465 q) (meaning1475 q) (meaning1480 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1475 = false ∨ valuation q 1480 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1481)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 4 (meaning1465 q) (meaning1476 q) (meaning1481 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1476 = false ∨ valuation q 1481 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1466)) (literal (valuationOf q) (1478)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 (meaning1466 q) (meaning1478 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1478 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1479)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 1 (meaning1466 q) (meaning1473 q) (meaning1479 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1473 = false ∨ valuation q 1479 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1480)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 2 (meaning1466 q) (meaning1474 q) (meaning1480 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1474 = false ∨ valuation q 1480 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 3 (meaning1466 q) (meaning1475 q) (meaning1481 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1475 = false ∨ valuation q 1481 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1482)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 4 (meaning1466 q) (meaning1476 q) (meaning1482 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1476 = false ∨ valuation q 1482 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1467)) (literal (valuationOf q) (1479)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 (meaning1467 q) (meaning1479 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1479 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1480)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 1 (meaning1467 q) (meaning1473 q) (meaning1480 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1473 = false ∨ valuation q 1480 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1481)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 2 (meaning1467 q) (meaning1474 q) (meaning1481 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1474 = false ∨ valuation q 1481 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1482)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 3 (meaning1467 q) (meaning1475 q) (meaning1482 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1475 = false ∨ valuation q 1482 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1483 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1483)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 4 (meaning1467 q) (meaning1476 q) (meaning1483 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1476 = false ∨ valuation q 1483 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1468)) (literal (valuationOf q) (1480)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 (meaning1468 q) (meaning1480 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1480 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1481)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 1 (meaning1468 q) (meaning1473 q) (meaning1481 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1473 = false ∨ valuation q 1481 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1482 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1482)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 2 (meaning1468 q) (meaning1474 q) (meaning1482 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1474 = false ∨ valuation q 1482 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1483 = true := by
  have hs : count1477 q = (countLit q [-16, -18, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1483)) (countLit q [-16, -18, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 3 (meaning1468 q) (meaning1475 q) (meaning1483 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1475 = false ∨ valuation q 1483 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1487)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 (meaning1479 q) (meaning1487 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1487 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1489)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 5 (meaning1481 q) (meaning1489 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1489 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1486)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 1 (meaning1454 q) (meaning1477 q) (meaning1486 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1477 = false ∨ valuation q 1486 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1487)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 2 (meaning1454 q) (meaning1478 q) (meaning1487 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1478 = false ∨ valuation q 1487 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1488)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 3 (meaning1454 q) (meaning1479 q) (meaning1488 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1479 = false ∨ valuation q 1488 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1489)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 4 (meaning1454 q) (meaning1480 q) (meaning1489 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1480 = false ∨ valuation q 1489 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E040.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112040
