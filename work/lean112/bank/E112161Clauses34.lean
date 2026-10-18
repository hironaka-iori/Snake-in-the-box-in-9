import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1513)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 3 1 (meaning1501 q) (meaning1506 q) (meaning1513 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1506 = false ∨ valuation q 1513 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1514 = true := by
  have hs : count1510 q = (countLit q [-85, -87, -88]) + (countLit q [-90, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-90, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (countLit q [-85, -87, -88]) (countLit q [-90, -93, -95, -97]) (count1510 q) 3 2 (meaning1501 q) (meaning1507 q) (meaning1514 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1507 = false ∨ valuation q 1514 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1517)) (countLit q [-101]) (countLit q [-103]) (count1517 q) 1 (meaningNeg103 q) (meaning1517 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1517 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1517)) (countLit q [-101]) (countLit q [-103]) (count1517 q) 1 (meaningNeg101 q) (meaning1517 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1517 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1518)) (countLit q [-101]) (countLit q [-103]) (count1517 q) 1 1 (meaningNeg101 q) (meaningNeg103 q) (meaning1518 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 1518 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-98]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101, -103])
  have hm := merge_right (literal (valuationOf q) (1517)) (literal (valuationOf q) (1519)) (countLit q [-98]) (countLit q [-101, -103]) (count1519 q) 1 (meaning1517 q) (meaning1519 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1519 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-98]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101, -103])
  have hm := merge_right (literal (valuationOf q) (1518)) (literal (valuationOf q) (1520)) (countLit q [-98]) (countLit q [-101, -103]) (count1519 q) 2 (meaning1518 q) (meaning1520 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1520 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-98]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101, -103])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1519)) (countLit q [-98]) (countLit q [-101, -103]) (count1519 q) 1 (meaningNeg98 q) (meaning1519 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1519 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1517 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-98]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101, -103])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1520)) (countLit q [-98]) (countLit q [-101, -103]) (count1519 q) 1 1 (meaningNeg98 q) (meaning1517 q) (meaning1520 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1517 = false ∨ valuation q 1520 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1518 = false ∨ valuationOf q 1521 = true := by
  have hs : count1519 q = (countLit q [-98]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101, -103])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1521)) (countLit q [-98]) (countLit q [-101, -103]) (count1519 q) 1 2 (meaningNeg98 q) (meaning1518 q) (meaning1521 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1518 = false ∨ valuation q 1521 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1522)) (countLit q [-104]) (countLit q [-106]) (count1522 q) 1 (meaningNeg106 q) (meaning1522 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1522 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1522)) (countLit q [-104]) (countLit q [-106]) (count1522 q) 1 (meaningNeg104 q) (meaning1522 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1522 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1524)) (countLit q [-109]) (countLit q [-111]) (count1524 q) 1 (meaningNeg111 q) (meaning1524 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1524 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1524)) (countLit q [-109]) (countLit q [-111]) (count1524 q) 1 (meaningNeg109 q) (meaning1524 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1524 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 111 = true ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-111)) (literal (valuationOf q) (1525)) (countLit q [-109]) (countLit q [-111]) (count1524 q) 1 1 (meaningNeg109 q) (meaningNeg111 q) (meaning1525 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 111)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 1525 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-104, -106]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-109, -111])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1526)) (countLit q [-104, -106]) (countLit q [-109, -111]) (count1526 q) 1 (meaning1524 q) (meaning1526 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1526 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-104, -106]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-109, -111])
  have hm := merge_right (literal (valuationOf q) (1525)) (literal (valuationOf q) (1527)) (countLit q [-104, -106]) (countLit q [-109, -111]) (count1526 q) 2 (meaning1525 q) (meaning1527 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1527 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-104, -106]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-109, -111])
  have hm := merge_left (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-104, -106]) (countLit q [-109, -111]) (count1526 q) 1 (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1526 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-104, -106]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1527)) (countLit q [-104, -106]) (countLit q [-109, -111]) (count1526 q) 1 1 (meaning1522 q) (meaning1524 q) (meaning1527 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = false ∨ valuation q 1527 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1528 = true := by
  have hs : count1526 q = (countLit q [-104, -106]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1528)) (countLit q [-104, -106]) (countLit q [-109, -111]) (count1526 q) 1 2 (meaning1522 q) (meaning1525 q) (meaning1528 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1525 = false ∨ valuation q 1528 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-98, -101, -103]) + (countLit q [-104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-98, -101, -103]) (l₂ := [-104, -106, -109, -111])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-98, -101, -103]) (countLit q [-104, -106, -109, -111]) (count1530 q) 1 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-98, -101, -103]) + (countLit q [-104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-98, -101, -103]) (l₂ := [-104, -106, -109, -111])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1531)) (countLit q [-98, -101, -103]) (countLit q [-104, -106, -109, -111]) (count1530 q) 2 (meaning1527 q) (meaning1531 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1531 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-98, -101, -103]) + (countLit q [-104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-98, -101, -103]) (l₂ := [-104, -106, -109, -111])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-98, -101, -103]) (countLit q [-104, -106, -109, -111]) (count1530 q) 3 (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1532 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-98, -101, -103]) + (countLit q [-104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-98, -101, -103]) (l₂ := [-104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1519)) (literal (valuationOf q) (1530)) (countLit q [-98, -101, -103]) (countLit q [-104, -106, -109, -111]) (count1530 q) 1 (meaning1519 q) (meaning1530 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1530 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-98, -101, -103]) + (countLit q [-104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-98, -101, -103]) (l₂ := [-104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1531)) (countLit q [-98, -101, -103]) (countLit q [-104, -106, -109, -111]) (count1530 q) 1 1 (meaning1519 q) (meaning1526 q) (meaning1531 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1526 = false ∨ valuation q 1531 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-98, -101, -103]) + (countLit q [-104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-98, -101, -103]) (l₂ := [-104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1520)) (literal (valuationOf q) (1531)) (countLit q [-98, -101, -103]) (countLit q [-104, -106, -109, -111]) (count1530 q) 2 (meaning1520 q) (meaning1531 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1531 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-98, -101, -103]) + (countLit q [-104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-98, -101, -103]) (l₂ := [-104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1532)) (countLit q [-98, -101, -103]) (countLit q [-104, -106, -109, -111]) (count1530 q) 2 1 (meaning1520 q) (meaning1526 q) (meaning1532 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1526 = false ∨ valuation q 1532 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-98, -101, -103]) + (countLit q [-104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-98, -101, -103]) (l₂ := [-104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1521)) (literal (valuationOf q) (1532)) (countLit q [-98, -101, -103]) (countLit q [-104, -106, -109, -111]) (count1530 q) 3 (meaning1521 q) (meaning1532 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1532 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_right (literal (valuationOf q) (1530)) (literal (valuationOf q) (1537)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 1 (meaning1530 q) (meaning1537 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1537 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1538)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 2 (meaning1531 q) (meaning1538 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1538 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_right (literal (valuationOf q) (1532)) (literal (valuationOf q) (1539)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 3 (meaning1532 q) (meaning1539 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1539 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1537)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 1 (meaning1510 q) (meaning1537 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1537 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E161.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112161
