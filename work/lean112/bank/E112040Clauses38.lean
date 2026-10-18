import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1572)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 8 6 (meaning1492 q) (meaning1549 q) (meaning1572 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1549 = false ∨ valuation q 1572 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1573)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 8 7 (meaning1492 q) (meaning1550 q) (meaning1573 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1550 = false ∨ valuation q 1573 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1574 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1574)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 8 8 (meaning1492 q) (meaning1551 q) (meaning1574 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1551 = false ∨ valuation q 1574 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1575 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1575)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 8 9 (meaning1492 q) (meaning1552 q) (meaning1575 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1552 = false ∨ valuation q 1575 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1570)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 9 3 (meaning1493 q) (meaning1546 q) (meaning1570 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1546 = false ∨ valuation q 1570 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1571)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 9 4 (meaning1493 q) (meaning1547 q) (meaning1571 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1547 = false ∨ valuation q 1571 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1572)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 9 5 (meaning1493 q) (meaning1548 q) (meaning1572 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1548 = false ∨ valuation q 1572 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1571)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 10 3 (meaning1494 q) (meaning1546 q) (meaning1571 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1546 = false ∨ valuation q 1571 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1572)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 10 4 (meaning1494 q) (meaning1547 q) (meaning1572 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1547 = false ∨ valuation q 1572 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1573)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 10 5 (meaning1494 q) (meaning1548 q) (meaning1573 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1548 = false ∨ valuation q 1573 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1580)) (countLit q [-62]) (countLit q [-63]) (count1580 q) 1 (meaningNeg63 q) (meaning1580 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1580 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1580)) (countLit q [-62]) (countLit q [-63]) (count1580 q) 1 (meaningNeg62 q) (meaning1580 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1580 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1581)) (countLit q [-62]) (countLit q [-63]) (count1580 q) 1 1 (meaningNeg62 q) (meaningNeg63 q) (meaning1581 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 1581 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (countLit q [-61]) (countLit q [-62, -63]) (count1582 q) 1 (meaning1580 q) (meaning1582 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-61]) (countLit q [-62, -63]) (count1582 q) 2 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1582)) (countLit q [-61]) (countLit q [-62, -63]) (count1582 q) 1 (meaningNeg61 q) (meaning1582 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1582 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1583)) (countLit q [-61]) (countLit q [-62, -63]) (count1582 q) 1 1 (meaningNeg61 q) (meaning1580 q) (meaning1583 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1580 = false ∨ valuation q 1583 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-61]) (countLit q [-62, -63]) (count1582 q) 1 2 (meaningNeg61 q) (meaning1581 q) (meaning1584 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-64]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1585)) (countLit q [-64]) (countLit q [-70]) (count1585 q) 1 (meaningNeg70 q) (meaning1585 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1585 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-64]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1585)) (countLit q [-64]) (countLit q [-70]) (count1585 q) 1 (meaningNeg64 q) (meaning1585 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1585 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-64]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1586)) (countLit q [-64]) (countLit q [-70]) (count1585 q) 1 1 (meaningNeg64 q) (meaningNeg70 q) (meaning1586 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 70 = true ∨ valuation q 1586 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1587)) (countLit q [-71]) (countLit q [-73]) (count1587 q) 1 (meaningNeg73 q) (meaning1587 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1587 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1587)) (countLit q [-71]) (countLit q [-73]) (count1587 q) 1 (meaningNeg71 q) (meaning1587 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1587 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1588)) (countLit q [-71]) (countLit q [-73]) (count1587 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning1588 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 1588 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-64, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -70]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1589)) (countLit q [-64, -70]) (countLit q [-71, -73]) (count1589 q) 1 (meaning1587 q) (meaning1589 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1589 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-64, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -70]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (countLit q [-64, -70]) (countLit q [-71, -73]) (count1589 q) 2 (meaning1588 q) (meaning1590 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-64, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -70]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-64, -70]) (countLit q [-71, -73]) (count1589 q) 1 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-64, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1590)) (countLit q [-64, -70]) (countLit q [-71, -73]) (count1589 q) 1 1 (meaning1585 q) (meaning1587 q) (meaning1590 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = false ∨ valuation q 1590 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-64, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1591)) (countLit q [-64, -70]) (countLit q [-71, -73]) (count1589 q) 1 2 (meaning1585 q) (meaning1588 q) (meaning1591 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1588 = false ∨ valuation q 1591 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-64, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -70]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-64, -70]) (countLit q [-71, -73]) (count1589 q) 2 (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1590 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-64, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-64, -70]) (countLit q [-71, -73]) (count1589 q) 2 1 (meaning1586 q) (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1589 q = (countLit q [-64, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-64, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-64, -70]) (countLit q [-71, -73]) (count1589 q) 2 2 (meaning1586 q) (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E040.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112040
