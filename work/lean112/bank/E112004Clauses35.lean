import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1451)) (literal (valuationOf q) (1455)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 2 (meaning1451 q) (meaning1455 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1455 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 3 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 4 (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1457 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1454)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 1 (meaning1443 q) (meaning1454 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1454 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1455)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 1 1 (meaning1443 q) (meaning1450 q) (meaning1455 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1450 = false ∨ valuation q 1455 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1456)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 1 2 (meaning1443 q) (meaning1451 q) (meaning1456 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1451 = false ∨ valuation q 1456 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1457)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 1 3 (meaning1443 q) (meaning1452 q) (meaning1457 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1452 = false ∨ valuation q 1457 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1455)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 2 (meaning1444 q) (meaning1455 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1455 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1456)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 2 1 (meaning1444 q) (meaning1450 q) (meaning1456 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1450 = false ∨ valuation q 1456 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1457)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 2 2 (meaning1444 q) (meaning1451 q) (meaning1457 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1451 = false ∨ valuation q 1457 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1457)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1454 q) 3 1 (meaning1445 q) (meaning1450 q) (meaning1457 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1450 = false ∨ valuation q 1457 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1461)) (countLit q [-18]) (countLit q [-20]) (count1461 q) 1 (meaningNeg20 q) (meaning1461 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1461 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1461)) (countLit q [-18]) (countLit q [-20]) (count1461 q) 1 (meaningNeg18 q) (meaning1461 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1461 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1462 = true := by
  have hs : count1461 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1462)) (countLit q [-18]) (countLit q [-20]) (count1461 q) 1 1 (meaningNeg18 q) (meaningNeg20 q) (meaning1462 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 1462 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1463)) (countLit q [-21]) (countLit q [-22]) (count1463 q) 1 (meaningNeg22 q) (meaning1463 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1463 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1463)) (countLit q [-21]) (countLit q [-22]) (count1463 q) 1 (meaningNeg21 q) (meaning1463 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1463 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1464)) (countLit q [-21]) (countLit q [-22]) (count1463 q) 1 1 (meaningNeg21 q) (meaningNeg22 q) (meaning1464 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 22 = true ∨ valuation q 1464 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-18, -20]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-21, -22])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (countLit q [-18, -20]) (countLit q [-21, -22]) (count1465 q) 1 (meaning1463 q) (meaning1465 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-18, -20]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-21, -22])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-18, -20]) (countLit q [-21, -22]) (count1465 q) 2 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-18, -20]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-21, -22])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1465)) (countLit q [-18, -20]) (countLit q [-21, -22]) (count1465 q) 1 (meaning1461 q) (meaning1465 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1465 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-18, -20]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (countLit q [-18, -20]) (countLit q [-21, -22]) (count1465 q) 1 1 (meaning1461 q) (meaning1463 q) (meaning1466 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1463 = false ∨ valuation q 1466 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-18, -20]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-18, -20]) (countLit q [-21, -22]) (count1465 q) 1 2 (meaning1461 q) (meaning1464 q) (meaning1467 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-18, -20]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-21, -22])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-18, -20]) (countLit q [-21, -22]) (count1465 q) 2 (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1466 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-18, -20]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-18, -20]) (countLit q [-21, -22]) (count1465 q) 2 1 (meaning1462 q) (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1463 = false ∨ valuation q 1467 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1465 q = (countLit q [-18, -20]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-18, -20]) (countLit q [-21, -22]) (count1465 q) 2 2 (meaning1462 q) (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = false ∨ valuation q 1468 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1469)) (countLit q [-24]) (countLit q [-26]) (count1469 q) 1 (meaningNeg26 q) (meaning1469 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1469 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1469)) (countLit q [-24]) (countLit q [-26]) (count1469 q) 1 (meaningNeg24 q) (meaning1469 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1469 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1470 = true := by
  have hs : count1469 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1470)) (countLit q [-24]) (countLit q [-26]) (count1469 q) 1 1 (meaningNeg24 q) (meaningNeg26 q) (meaning1470 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 1470 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1471)) (countLit q [-28]) (countLit q [-30]) (count1471 q) 1 (meaningNeg30 q) (meaning1471 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1471 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1471)) (countLit q [-28]) (countLit q [-30]) (count1471 q) 1 (meaningNeg28 q) (meaning1471 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1471 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1472 = true := by
  have hs : count1471 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1472)) (countLit q [-28]) (countLit q [-30]) (count1471 q) 1 1 (meaningNeg28 q) (meaningNeg30 q) (meaning1472 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 30 = true ∨ valuation q 1472 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 1 (meaning1471 q) (meaning1473 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E004.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112004
