import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1480)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 1 2 (meaning1467 q) (meaning1475 q) (meaning1480 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1475 = false ∨ valuation q 1480 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1481)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 1 3 (meaning1467 q) (meaning1476 q) (meaning1481 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1476 = false ∨ valuation q 1481 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1482 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1482)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 1 4 (meaning1467 q) (meaning1477 q) (meaning1482 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1477 = false ∨ valuation q 1482 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1468)) (literal (valuationOf q) (1479)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 2 (meaning1468 q) (meaning1479 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1479 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1480)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 2 1 (meaning1468 q) (meaning1474 q) (meaning1480 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1474 = false ∨ valuation q 1480 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 2 2 (meaning1468 q) (meaning1475 q) (meaning1481 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1475 = false ∨ valuation q 1481 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1482)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 2 3 (meaning1468 q) (meaning1476 q) (meaning1482 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1476 = false ∨ valuation q 1482 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1481)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 3 1 (meaning1469 q) (meaning1474 q) (meaning1481 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1474 = false ∨ valuation q 1481 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1482)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 3 2 (meaning1469 q) (meaning1475 q) (meaning1482 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1475 = false ∨ valuation q 1482 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1485)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 (meaning1478 q) (meaning1485 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1485 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1486)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 (meaning1479 q) (meaning1486 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1486 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1487)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 (meaning1480 q) (meaning1487 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1487 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 (meaning1481 q) (meaning1488 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1488 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 5 (meaning1482 q) (meaning1489 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1489 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1458)) (literal (valuationOf q) (1485)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 (meaning1458 q) (meaning1485 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1485 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1486)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 1 (meaning1458 q) (meaning1478 q) (meaning1486 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1478 = false ∨ valuation q 1486 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1487)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 2 (meaning1458 q) (meaning1479 q) (meaning1487 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1479 = false ∨ valuation q 1487 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 3 (meaning1458 q) (meaning1480 q) (meaning1488 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1480 = false ∨ valuation q 1488 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 4 (meaning1458 q) (meaning1481 q) (meaning1489 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1481 = false ∨ valuation q 1489 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 5 (meaning1458 q) (meaning1482 q) (meaning1490 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1482 = false ∨ valuation q 1490 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1459)) (literal (valuationOf q) (1486)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 (meaning1459 q) (meaning1486 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1486 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1487)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 1 (meaning1459 q) (meaning1478 q) (meaning1487 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1478 = false ∨ valuation q 1487 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 2 (meaning1459 q) (meaning1479 q) (meaning1488 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1479 = false ∨ valuation q 1488 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 3 (meaning1459 q) (meaning1480 q) (meaning1489 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1480 = false ∨ valuation q 1489 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 4 (meaning1459 q) (meaning1481 q) (meaning1490 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1481 = false ∨ valuation q 1490 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1491)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 5 (meaning1459 q) (meaning1482 q) (meaning1491 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1482 = false ∨ valuation q 1491 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1487)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 (meaning1460 q) (meaning1487 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1487 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 1 (meaning1460 q) (meaning1478 q) (meaning1488 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1478 = false ∨ valuation q 1488 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 2 (meaning1460 q) (meaning1479 q) (meaning1489 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1479 = false ∨ valuation q 1489 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 3 (meaning1460 q) (meaning1480 q) (meaning1490 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1480 = false ∨ valuation q 1490 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1492)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 5 (meaning1460 q) (meaning1482 q) (meaning1492 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1482 = false ∨ valuation q 1492 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 (meaning1461 q) (meaning1488 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1488 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E047.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112047
