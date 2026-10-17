import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 5 (meaning1454 q) (meaning1481 q) (meaning1490 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1481 = false ∨ valuation q 1490 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 6 (meaning1454 q) (meaning1482 q) (meaning1491 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1482 = false ∨ valuation q 1491 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 7 (meaning1454 q) (meaning1483 q) (meaning1492 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1483 = false ∨ valuation q 1492 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 2 (meaning1455 q) (meaning1478 q) (meaning1488 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1478 = false ∨ valuation q 1488 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 3 (meaning1455 q) (meaning1479 q) (meaning1489 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1479 = false ∨ valuation q 1489 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 4 (meaning1455 q) (meaning1480 q) (meaning1490 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1480 = false ∨ valuation q 1490 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 5 (meaning1455 q) (meaning1481 q) (meaning1491 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1481 = false ∨ valuation q 1491 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 6 (meaning1455 q) (meaning1482 q) (meaning1492 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1482 = false ∨ valuation q 1492 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 2 (meaning1456 q) (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1478 = false ∨ valuation q 1489 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 3 (meaning1456 q) (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1479 = false ∨ valuation q 1490 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 3 4 (meaning1456 q) (meaning1480 q) (meaning1491 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1480 = false ∨ valuation q 1491 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 1 (meaning1457 q) (meaning1477 q) (meaning1489 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1477 = false ∨ valuation q 1489 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 2 (meaning1457 q) (meaning1478 q) (meaning1490 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1478 = false ∨ valuation q 1490 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 4 (meaning1457 q) (meaning1480 q) (meaning1492 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1480 = false ∨ valuation q 1492 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1500)) (countLit q [-35]) (countLit q [-36]) (count1500 q) 1 (meaningNeg36 q) (meaning1500 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1500 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1500)) (countLit q [-35]) (countLit q [-36]) (count1500 q) 1 (meaningNeg35 q) (meaning1500 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1500 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1501)) (countLit q [-35]) (countLit q [-36]) (count1500 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning1501 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 1501 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -36])
  have hm := merge_right (literal (valuationOf q) (1500)) (literal (valuationOf q) (1502)) (countLit q [-32]) (countLit q [-35, -36]) (count1502 q) 1 (meaning1500 q) (meaning1502 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1502 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -36])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1503)) (countLit q [-32]) (countLit q [-35, -36]) (count1502 q) 2 (meaning1501 q) (meaning1503 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1503 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -36])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1502)) (countLit q [-32]) (countLit q [-35, -36]) (count1502 q) 1 (meaningNeg32 q) (meaning1502 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1502 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1500 = false ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1503)) (countLit q [-32]) (countLit q [-35, -36]) (count1502 q) 1 1 (meaningNeg32 q) (meaning1500 q) (meaning1503 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1500 = false ∨ valuation q 1503 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1504)) (countLit q [-32]) (countLit q [-35, -36]) (count1502 q) 1 2 (meaningNeg32 q) (meaning1501 q) (meaning1504 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1501 = false ∨ valuation q 1504 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1505)) (countLit q [-38]) (countLit q [-40]) (count1505 q) 1 (meaningNeg40 q) (meaning1505 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1505 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1505)) (countLit q [-38]) (countLit q [-40]) (count1505 q) 1 (meaningNeg38 q) (meaning1505 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1505 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1506)) (countLit q [-38]) (countLit q [-40]) (count1505 q) 1 1 (meaningNeg38 q) (meaningNeg40 q) (meaning1506 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 1506 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1507)) (countLit q [-42]) (countLit q [-44]) (count1507 q) 1 (meaningNeg44 q) (meaning1507 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1507 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1507)) (countLit q [-42]) (countLit q [-44]) (count1507 q) 1 (meaningNeg42 q) (meaning1507 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1507 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1508)) (countLit q [-42]) (countLit q [-44]) (count1507 q) 1 1 (meaningNeg42 q) (meaningNeg44 q) (meaning1508 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 44 = true ∨ valuation q 1508 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = true := by
  have hs : count1509 q = (countLit q [-38, -40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (countLit q [-38, -40]) (countLit q [-42, -44]) (count1509 q) 1 (meaning1507 q) (meaning1509 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1510 = true := by
  have hs : count1509 q = (countLit q [-38, -40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1510)) (countLit q [-38, -40]) (countLit q [-42, -44]) (count1509 q) 2 (meaning1508 q) (meaning1510 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1510 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1509 q = (countLit q [-38, -40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-38, -40]) (countLit q [-42, -44]) (count1509 q) 1 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1510 = true := by
  have hs : count1509 q = (countLit q [-38, -40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1510)) (countLit q [-38, -40]) (countLit q [-42, -44]) (count1509 q) 1 1 (meaning1505 q) (meaning1507 q) (meaning1510 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = false ∨ valuation q 1510 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E004.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112004
