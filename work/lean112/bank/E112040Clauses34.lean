import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1515)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 3 (meaning1504 q) (meaning1515 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1515 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1516 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1516)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 3 1 (meaning1504 q) (meaning1509 q) (meaning1516 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1509 = false ∨ valuation q 1516 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1517)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 3 2 (meaning1504 q) (meaning1510 q) (meaning1517 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1510 = false ∨ valuation q 1517 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1518)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 3 3 (meaning1504 q) (meaning1511 q) (meaning1518 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1511 = false ∨ valuation q 1518 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1519 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1519)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 3 4 (meaning1504 q) (meaning1512 q) (meaning1519 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1512 = false ∨ valuation q 1519 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1520)) (countLit q [-46]) (countLit q [-47]) (count1520 q) 1 (meaningNeg47 q) (meaning1520 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1520 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1520)) (countLit q [-46]) (countLit q [-47]) (count1520 q) 1 (meaningNeg46 q) (meaning1520 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1520 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1521 = true := by
  have hs : count1520 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1521)) (countLit q [-46]) (countLit q [-47]) (count1520 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning1521 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 1521 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1522)) (countLit q [-48]) (countLit q [-50]) (count1522 q) 1 (meaningNeg50 q) (meaning1522 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1522 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1522)) (countLit q [-48]) (countLit q [-50]) (count1522 q) 1 (meaningNeg48 q) (meaning1522 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1522 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 50 = true ∨ valuationOf q 1523 = true := by
  have hs : count1522 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (1523)) (countLit q [-48]) (countLit q [-50]) (count1522 q) 1 1 (meaningNeg48 q) (meaningNeg50 q) (meaning1523 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 1523 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (1522)) (literal (valuationOf q) (1524)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1524 q) 1 (meaning1522 q) (meaning1524 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (1523)) (literal (valuationOf q) (1525)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1524 q) 2 (meaning1523 q) (meaning1525 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1525 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_left (literal (valuationOf q) (1520)) (literal (valuationOf q) (1524)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1524 q) 1 (meaning1520 q) (meaning1524 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1524 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1525)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1524 q) 1 1 (meaning1520 q) (meaning1522 q) (meaning1525 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1522 = false ∨ valuation q 1525 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1526)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1524 q) 1 2 (meaning1520 q) (meaning1523 q) (meaning1526 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1523 = false ∨ valuation q 1526 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_left (literal (valuationOf q) (1521)) (literal (valuationOf q) (1525)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1524 q) 2 (meaning1521 q) (meaning1525 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1525 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1524 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1524 q) 2 1 (meaning1521 q) (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1522 = false ∨ valuation q 1526 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1527 = true := by
  have hs : count1524 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1527)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1524 q) 2 2 (meaning1521 q) (meaning1523 q) (meaning1527 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1523 = false ∨ valuation q 1527 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1528)) (countLit q [-52]) (countLit q [-54]) (count1528 q) 1 (meaningNeg54 q) (meaning1528 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1528 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1528)) (countLit q [-52]) (countLit q [-54]) (count1528 q) 1 (meaningNeg52 q) (meaning1528 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1528 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1529)) (countLit q [-52]) (countLit q [-54]) (count1528 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning1529 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 1529 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1530)) (countLit q [-56]) (countLit q [-58]) (count1530 q) 1 (meaningNeg58 q) (meaning1530 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1530 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1530)) (countLit q [-56]) (countLit q [-58]) (count1530 q) 1 (meaningNeg56 q) (meaning1530 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1530 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1531)) (countLit q [-56]) (countLit q [-58]) (count1530 q) 1 1 (meaningNeg56 q) (meaningNeg58 q) (meaning1531 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 58 = true ∨ valuation q 1531 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1532 = true := by
  have hs : count1532 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (1530)) (literal (valuationOf q) (1532)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1532 q) 1 (meaning1530 q) (meaning1532 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1532 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1532 q) 2 (meaning1531 q) (meaning1533 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1532 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_left (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1532 q) 1 (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1532 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1533)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1532 q) 1 1 (meaning1528 q) (meaning1530 q) (meaning1533 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = false ∨ valuation q 1533 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true := by
  have hs : count1532 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1532 q) 1 2 (meaning1528 q) (meaning1531 q) (meaning1534 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1531 = false ∨ valuation q 1534 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_left (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1532 q) 2 (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1533 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1532 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1532 q) 2 1 (meaning1529 q) (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1530 = false ∨ valuation q 1534 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E040.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112040
