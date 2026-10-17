import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 1 (meaning1461 q) (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1478 = false ∨ valuation q 1489 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 2 (meaning1461 q) (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1479 = false ∨ valuation q 1490 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1491)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 3 (meaning1461 q) (meaning1480 q) (meaning1491 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1480 = false ∨ valuation q 1491 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1492)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 4 (meaning1461 q) (meaning1481 q) (meaning1492 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1481 = false ∨ valuation q 1492 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 5 (meaning1462 q) (meaning1489 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1489 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 5 1 (meaning1462 q) (meaning1478 q) (meaning1490 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1478 = false ∨ valuation q 1490 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1491)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 5 2 (meaning1462 q) (meaning1479 q) (meaning1491 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1479 = false ∨ valuation q 1491 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1492)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 5 3 (meaning1462 q) (meaning1480 q) (meaning1492 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1480 = false ∨ valuation q 1492 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1463)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 6 (meaning1463 q) (meaning1490 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1490 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1491)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 6 1 (meaning1463 q) (meaning1478 q) (meaning1491 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1478 = false ∨ valuation q 1491 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1499)) (countLit q [-36]) (countLit q [-37]) (count1499 q) 1 (meaningNeg37 q) (meaning1499 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1499 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1499)) (countLit q [-36]) (countLit q [-37]) (count1499 q) 1 (meaningNeg36 q) (meaning1499 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1499 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1500)) (countLit q [-36]) (countLit q [-37]) (count1499 q) 1 1 (meaningNeg36 q) (meaningNeg37 q) (meaning1500 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 1500 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_right (literal (valuationOf q) (1499)) (literal (valuationOf q) (1501)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 1 (meaning1499 q) (meaning1501 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1501 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_right (literal (valuationOf q) (1500)) (literal (valuationOf q) (1502)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 2 (meaning1500 q) (meaning1502 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1502 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1501)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 1 (meaningNeg34 q) (meaning1501 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1501 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1499 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1502)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 1 1 (meaningNeg34 q) (meaning1499 q) (meaning1502 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1499 = false ∨ valuation q 1502 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1500 = false ∨ valuationOf q 1503 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1503)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 1 2 (meaningNeg34 q) (meaning1500 q) (meaning1503 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1500 = false ∨ valuation q 1503 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1504)) (countLit q [-40]) (countLit q [-42]) (count1504 q) 1 (meaningNeg42 q) (meaning1504 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1504 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1504)) (countLit q [-40]) (countLit q [-42]) (count1504 q) 1 (meaningNeg40 q) (meaning1504 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1504 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1505)) (countLit q [-40]) (countLit q [-42]) (count1504 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1505 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1505 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1506)) (countLit q [-43]) (countLit q [-46]) (count1506 q) 1 (meaningNeg46 q) (meaning1506 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1506 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1506)) (countLit q [-43]) (countLit q [-46]) (count1506 q) 1 (meaningNeg43 q) (meaning1506 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1506 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1507)) (countLit q [-43]) (countLit q [-46]) (count1506 q) 1 1 (meaningNeg43 q) (meaningNeg46 q) (meaning1507 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 46 = true ∨ valuation q 1507 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 1 (meaning1506 q) (meaning1508 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 2 (meaning1507 q) (meaning1509 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 1 (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1508 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 1 1 (meaning1504 q) (meaning1506 q) (meaning1509 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = false ∨ valuation q 1509 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1510)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 1 2 (meaning1504 q) (meaning1507 q) (meaning1510 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1507 = false ∨ valuation q 1510 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 2 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 2 1 (meaning1505 q) (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1506 = false ∨ valuation q 1510 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-40, -42]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-40, -42]) (countLit q [-43, -46]) (count1508 q) 2 2 (meaning1505 q) (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = false ∨ valuation q 1511 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E047.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112047
