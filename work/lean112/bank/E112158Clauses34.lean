import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1465 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1465)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 2 3 (meaning1435 q) (meaning1456 q) (meaning1465 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1456 = false ∨ valuation q 1465 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1466 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1466)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 2 4 (meaning1435 q) (meaning1457 q) (meaning1466 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1457 = false ∨ valuation q 1466 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1467 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1467)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 2 5 (meaning1435 q) (meaning1458 q) (meaning1467 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1458 = false ∨ valuation q 1467 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1464)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 3 1 (meaning1436 q) (meaning1454 q) (meaning1464 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1454 = false ∨ valuation q 1464 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1465 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1465)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 3 2 (meaning1436 q) (meaning1455 q) (meaning1465 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1455 = false ∨ valuation q 1465 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1466 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1466)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 3 3 (meaning1436 q) (meaning1456 q) (meaning1466 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1456 = false ∨ valuation q 1466 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1468 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1468)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 3 5 (meaning1436 q) (meaning1458 q) (meaning1468 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1458 = false ∨ valuation q 1468 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1465 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1465)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 4 1 (meaning1437 q) (meaning1454 q) (meaning1465 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1454 = false ∨ valuation q 1465 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1466 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1466)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 4 2 (meaning1437 q) (meaning1455 q) (meaning1466 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1455 = false ∨ valuation q 1466 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1467 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1467)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 4 3 (meaning1437 q) (meaning1456 q) (meaning1467 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1456 = false ∨ valuation q 1467 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1466 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1466)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 5 1 (meaning1438 q) (meaning1454 q) (meaning1466 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1454 = false ∨ valuation q 1466 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1467 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1467)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 5 2 (meaning1438 q) (meaning1455 q) (meaning1467 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1455 = false ∨ valuation q 1467 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1475)) (countLit q [-34]) (countLit q [-35]) (count1475 q) 1 (meaningNeg35 q) (meaning1475 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1475 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1475)) (countLit q [-34]) (countLit q [-35]) (count1475 q) 1 (meaningNeg34 q) (meaning1475 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1475 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1476)) (countLit q [-34]) (countLit q [-35]) (count1475 q) 1 1 (meaningNeg34 q) (meaningNeg35 q) (meaning1476 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 1476 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1477)) (countLit q [-32]) (countLit q [-34, -35]) (count1477 q) 1 (meaning1475 q) (meaning1477 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1477 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1478)) (countLit q [-32]) (countLit q [-34, -35]) (count1477 q) 2 (meaning1476 q) (meaning1478 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1478 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1477)) (countLit q [-32]) (countLit q [-34, -35]) (count1477 q) 1 (meaningNeg32 q) (meaning1477 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1477 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1478)) (countLit q [-32]) (countLit q [-34, -35]) (count1477 q) 1 1 (meaningNeg32 q) (meaning1475 q) (meaning1478 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1475 = false ∨ valuation q 1478 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1479)) (countLit q [-32]) (countLit q [-34, -35]) (count1477 q) 1 2 (meaningNeg32 q) (meaning1476 q) (meaning1479 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1476 = false ∨ valuation q 1479 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1480)) (countLit q [-39]) (countLit q [-41]) (count1480 q) 1 (meaningNeg41 q) (meaning1480 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1480 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1480)) (countLit q [-39]) (countLit q [-41]) (count1480 q) 1 (meaningNeg39 q) (meaning1480 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1480 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1481)) (countLit q [-39]) (countLit q [-41]) (count1480 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning1481 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 1481 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1482)) (countLit q [-42]) (countLit q [-44]) (count1482 q) 1 (meaningNeg44 q) (meaning1482 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1482 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1482)) (countLit q [-42]) (countLit q [-44]) (count1482 q) 1 (meaningNeg42 q) (meaning1482 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1482 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1483)) (countLit q [-42]) (countLit q [-44]) (count1482 q) 1 1 (meaningNeg42 q) (meaningNeg44 q) (meaning1483 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 44 = true ∨ valuation q 1483 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-39, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1484)) (countLit q [-39, -41]) (countLit q [-42, -44]) (count1484 q) 1 (meaning1482 q) (meaning1484 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1484 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-39, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1485)) (countLit q [-39, -41]) (countLit q [-42, -44]) (count1484 q) 2 (meaning1483 q) (meaning1485 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1485 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-39, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-39, -41]) (countLit q [-42, -44]) (count1484 q) 1 (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1484 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-39, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1485)) (countLit q [-39, -41]) (countLit q [-42, -44]) (count1484 q) 1 1 (meaning1480 q) (meaning1482 q) (meaning1485 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1482 = false ∨ valuation q 1485 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-39, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1486)) (countLit q [-39, -41]) (countLit q [-42, -44]) (count1484 q) 1 2 (meaning1480 q) (meaning1483 q) (meaning1486 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1483 = false ∨ valuation q 1486 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-39, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (1481)) (literal (valuationOf q) (1485)) (countLit q [-39, -41]) (countLit q [-42, -44]) (count1484 q) 2 (meaning1481 q) (meaning1485 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E158.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112158
