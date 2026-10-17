import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1479)) (countLit q [-46]) (countLit q [-49]) (count1479 q) 1 (meaningNeg46 q) (meaning1479 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1479 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1480)) (countLit q [-46]) (countLit q [-49]) (count1479 q) 1 1 (meaningNeg46 q) (meaningNeg49 q) (meaning1480 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 49 = true ∨ valuation q 1480 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-43, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-46, -49])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1481)) (countLit q [-43, -44]) (countLit q [-46, -49]) (count1481 q) 1 (meaning1479 q) (meaning1481 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1481 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-43, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-46, -49])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1482)) (countLit q [-43, -44]) (countLit q [-46, -49]) (count1481 q) 2 (meaning1480 q) (meaning1482 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1482 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-43, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-46, -49])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-43, -44]) (countLit q [-46, -49]) (count1481 q) 1 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-43, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1482)) (countLit q [-43, -44]) (countLit q [-46, -49]) (count1481 q) 1 1 (meaning1477 q) (meaning1479 q) (meaning1482 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = false ∨ valuation q 1482 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-43, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1483)) (countLit q [-43, -44]) (countLit q [-46, -49]) (count1481 q) 1 2 (meaning1477 q) (meaning1480 q) (meaning1483 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1480 = false ∨ valuation q 1483 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-43, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-46, -49])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-43, -44]) (countLit q [-46, -49]) (count1481 q) 2 (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1482 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-43, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-43, -44]) (countLit q [-46, -49]) (count1481 q) 2 1 (meaning1478 q) (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1479 = false ∨ valuation q 1483 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1481 q = (countLit q [-43, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-43, -44]) (countLit q [-46, -49]) (count1481 q) 2 2 (meaning1478 q) (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1480 = false ∨ valuation q 1484 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1485)) (countLit q [-50]) (countLit q [-51]) (count1485 q) 1 (meaningNeg51 q) (meaning1485 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1485 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1485)) (countLit q [-50]) (countLit q [-51]) (count1485 q) 1 (meaningNeg50 q) (meaning1485 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1485 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1486)) (countLit q [-50]) (countLit q [-51]) (count1485 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning1486 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 1486 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1487)) (countLit q [-52]) (countLit q [-56]) (count1487 q) 1 (meaningNeg56 q) (meaning1487 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1487 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1487)) (countLit q [-52]) (countLit q [-56]) (count1487 q) 1 (meaningNeg52 q) (meaning1487 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1487 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1488)) (countLit q [-52]) (countLit q [-56]) (count1487 q) 1 1 (meaningNeg52 q) (meaningNeg56 q) (meaning1488 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 56 = true ∨ valuation q 1488 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-50, -51]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-52, -56])
  have hm := merge_right (literal (valuationOf q) (1487)) (literal (valuationOf q) (1489)) (countLit q [-50, -51]) (countLit q [-52, -56]) (count1489 q) 1 (meaning1487 q) (meaning1489 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1489 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-50, -51]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-52, -56])
  have hm := merge_right (literal (valuationOf q) (1488)) (literal (valuationOf q) (1490)) (countLit q [-50, -51]) (countLit q [-52, -56]) (count1489 q) 2 (meaning1488 q) (meaning1490 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1490 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-50, -51]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-52, -56])
  have hm := merge_left (literal (valuationOf q) (1485)) (literal (valuationOf q) (1489)) (countLit q [-50, -51]) (countLit q [-52, -56]) (count1489 q) 1 (meaning1485 q) (meaning1489 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1489 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-50, -51]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-52, -56])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1490)) (countLit q [-50, -51]) (countLit q [-52, -56]) (count1489 q) 1 1 (meaning1485 q) (meaning1487 q) (meaning1490 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1487 = false ∨ valuation q 1490 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1491 = true := by
  have hs : count1489 q = (countLit q [-50, -51]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-52, -56])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1491)) (countLit q [-50, -51]) (countLit q [-52, -56]) (count1489 q) 1 2 (meaning1485 q) (meaning1488 q) (meaning1491 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1488 = false ∨ valuation q 1491 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-50, -51]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-52, -56])
  have hm := merge_left (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-50, -51]) (countLit q [-52, -56]) (count1489 q) 2 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1491 = true := by
  have hs : count1489 q = (countLit q [-50, -51]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-52, -56])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1491)) (countLit q [-50, -51]) (countLit q [-52, -56]) (count1489 q) 2 1 (meaning1486 q) (meaning1487 q) (meaning1491 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1487 = false ∨ valuation q 1491 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1493 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_right (literal (valuationOf q) (1489)) (literal (valuationOf q) (1493)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 1 (meaning1489 q) (meaning1493 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1493 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1494 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_right (literal (valuationOf q) (1490)) (literal (valuationOf q) (1494)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 2 (meaning1490 q) (meaning1494 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1494 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1493 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1481)) (literal (valuationOf q) (1493)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 1 (meaning1481 q) (meaning1493 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1493 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1494 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1494)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 1 1 (meaning1481 q) (meaning1489 q) (meaning1494 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1489 = false ∨ valuation q 1494 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1495 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1495)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 1 2 (meaning1481 q) (meaning1490 q) (meaning1495 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1490 = false ∨ valuation q 1495 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1496 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1496)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 1 3 (meaning1481 q) (meaning1491 q) (meaning1496 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1491 = false ∨ valuation q 1496 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1494 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1482)) (literal (valuationOf q) (1494)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 2 (meaning1482 q) (meaning1494 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1494 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1495 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1495)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 2 1 (meaning1482 q) (meaning1489 q) (meaning1495 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1489 = false ∨ valuation q 1495 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1496 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1496)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 2 2 (meaning1482 q) (meaning1490 q) (meaning1496 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1490 = false ∨ valuation q 1496 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E064.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112064
