import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1490)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 5 (meaning1454 q) (meaning1481 q) (meaning1490 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1481 = false ∨ valuation q 1490 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1491)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 6 (meaning1454 q) (meaning1482 q) (meaning1491 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1482 = false ∨ valuation q 1491 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1492)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 7 (meaning1454 q) (meaning1483 q) (meaning1492 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1483 = false ∨ valuation q 1492 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1487)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 1 (meaning1455 q) (meaning1477 q) (meaning1487 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1477 = false ∨ valuation q 1487 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1488)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 2 (meaning1455 q) (meaning1478 q) (meaning1488 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1478 = false ∨ valuation q 1488 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1489)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 3 (meaning1455 q) (meaning1479 q) (meaning1489 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1479 = false ∨ valuation q 1489 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1490)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 4 (meaning1455 q) (meaning1480 q) (meaning1490 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1480 = false ∨ valuation q 1490 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1491)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 5 (meaning1455 q) (meaning1481 q) (meaning1491 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1481 = false ∨ valuation q 1491 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1492)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 6 (meaning1455 q) (meaning1482 q) (meaning1492 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1482 = false ∨ valuation q 1492 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1493)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 7 (meaning1455 q) (meaning1483 q) (meaning1493 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1483 = false ∨ valuation q 1493 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1456)) (literal (valuationOf q) (1487)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 (meaning1456 q) (meaning1487 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1487 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1488)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 1 (meaning1456 q) (meaning1477 q) (meaning1488 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1477 = false ∨ valuation q 1488 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 2 (meaning1456 q) (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1478 = false ∨ valuation q 1489 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 3 (meaning1456 q) (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1479 = false ∨ valuation q 1490 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1491)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 4 (meaning1456 q) (meaning1480 q) (meaning1491 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1480 = false ∨ valuation q 1491 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1492)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 5 (meaning1456 q) (meaning1481 q) (meaning1492 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1481 = false ∨ valuation q 1492 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1493 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1493)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 6 (meaning1456 q) (meaning1482 q) (meaning1493 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1482 = false ∨ valuation q 1493 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1494)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 7 (meaning1456 q) (meaning1483 q) (meaning1494 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1483 = false ∨ valuation q 1494 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1489)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 1 (meaning1457 q) (meaning1477 q) (meaning1489 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1477 = false ∨ valuation q 1489 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1490)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 2 (meaning1457 q) (meaning1478 q) (meaning1490 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1478 = false ∨ valuation q 1490 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1491)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 3 (meaning1457 q) (meaning1479 q) (meaning1491 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1479 = false ∨ valuation q 1491 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1492)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 4 (meaning1457 q) (meaning1480 q) (meaning1492 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1480 = false ∨ valuation q 1492 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1493 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1493)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 5 (meaning1457 q) (meaning1481 q) (meaning1493 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1481 = false ∨ valuation q 1493 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1494 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1494)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 6 (meaning1457 q) (meaning1482 q) (meaning1494 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1482 = false ∨ valuation q 1494 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1490)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 5 1 (meaning1458 q) (meaning1477 q) (meaning1490 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1477 = false ∨ valuation q 1490 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1491)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 5 2 (meaning1458 q) (meaning1478 q) (meaning1491 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1478 = false ∨ valuation q 1491 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1492)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 5 3 (meaning1458 q) (meaning1479 q) (meaning1492 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1479 = false ∨ valuation q 1492 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1493 = true := by
  have hs : count1485 q = (countLit q [-3, -4, -6, -7, -9, -12, -15]) + (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15]) (l₂ := [-16, -18, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1493)) (countLit q [-3, -4, -6, -7, -9, -12, -15]) (countLit q [-16, -18, -21, -22, -24, -26, -28, -30]) (count1485 q) 5 4 (meaning1458 q) (meaning1480 q) (meaning1493 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1480 = false ∨ valuation q 1493 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1500)) (countLit q [-34]) (countLit q [-37]) (count1500 q) 1 (meaningNeg37 q) (meaning1500 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1500 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1500)) (countLit q [-34]) (countLit q [-37]) (count1500 q) 1 (meaningNeg34 q) (meaning1500 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1500 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1501)) (countLit q [-34]) (countLit q [-37]) (count1500 q) 1 1 (meaningNeg34 q) (meaningNeg37 q) (meaning1501 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 1501 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -37])
  have hm := merge_right (literal (valuationOf q) (1500)) (literal (valuationOf q) (1502)) (countLit q [-32]) (countLit q [-34, -37]) (count1502 q) 1 (meaning1500 q) (meaning1502 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1502 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E040.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112040
