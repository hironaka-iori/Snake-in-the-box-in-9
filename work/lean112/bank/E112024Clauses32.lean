import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1580 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1580)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 7 8 (meaning1493 q) (meaning1557 q) (meaning1580 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1557 = false ∨ valuation q 1580 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1581 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1581)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 7 9 (meaning1493 q) (meaning1558 q) (meaning1581 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1558 = false ∨ valuation q 1581 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 8 2 (meaning1494 q) (meaning1551 q) (meaning1575 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1551 = false ∨ valuation q 1575 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1576 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1576)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 8 3 (meaning1494 q) (meaning1552 q) (meaning1576 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1552 = false ∨ valuation q 1576 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 8 4 (meaning1494 q) (meaning1553 q) (meaning1577 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1553 = false ∨ valuation q 1577 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1578 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1578)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 8 5 (meaning1494 q) (meaning1554 q) (meaning1578 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1554 = false ∨ valuation q 1578 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1579 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1579)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 8 6 (meaning1494 q) (meaning1555 q) (meaning1579 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1555 = false ∨ valuation q 1579 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1580 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1580)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 8 7 (meaning1494 q) (meaning1556 q) (meaning1580 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1556 = false ∨ valuation q 1580 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1581 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1581)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 8 8 (meaning1494 q) (meaning1557 q) (meaning1581 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1557 = false ∨ valuation q 1581 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1576 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1576)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 9 2 (meaning1495 q) (meaning1551 q) (meaning1576 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1551 = false ∨ valuation q 1576 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 9 3 (meaning1495 q) (meaning1552 q) (meaning1577 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1552 = false ∨ valuation q 1577 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1578 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1578)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 9 4 (meaning1495 q) (meaning1553 q) (meaning1578 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1553 = false ∨ valuation q 1578 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1579 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1579)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 9 5 (meaning1495 q) (meaning1554 q) (meaning1579 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1554 = false ∨ valuation q 1579 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1580 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1580)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 9 6 (meaning1495 q) (meaning1555 q) (meaning1580 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1555 = false ∨ valuation q 1580 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 10 2 (meaning1496 q) (meaning1551 q) (meaning1577 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1551 = false ∨ valuation q 1577 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1578 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1578)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 10 3 (meaning1496 q) (meaning1552 q) (meaning1578 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1552 = false ∨ valuation q 1578 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1579 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1579)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 10 4 (meaning1496 q) (meaning1553 q) (meaning1579 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1553 = false ∨ valuation q 1579 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1589)) (countLit q [-58]) (countLit q [-61]) (count1589 q) 1 (meaningNeg61 q) (meaning1589 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1589 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1589)) (countLit q [-58]) (countLit q [-61]) (count1589 q) 1 (meaningNeg58 q) (meaning1589 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1589 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 61 = true ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (1590)) (countLit q [-58]) (countLit q [-61]) (count1589 q) 1 1 (meaningNeg58 q) (meaningNeg61 q) (meaning1590 q) hs
  change (! (valuationOf q 58)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 1590 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1591)) (countLit q [-62]) (countLit q [-63]) (count1591 q) 1 (meaningNeg63 q) (meaning1591 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1591 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1591)) (countLit q [-62]) (countLit q [-63]) (count1591 q) 1 (meaningNeg62 q) (meaning1591 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1591 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1592)) (countLit q [-62]) (countLit q [-63]) (count1591 q) 1 1 (meaningNeg62 q) (meaningNeg63 q) (meaning1592 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 1592 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-58, -61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1593)) (countLit q [-58, -61]) (countLit q [-62, -63]) (count1593 q) 1 (meaning1591 q) (meaning1593 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1593 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-58, -61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-62, -63])
  have hm := merge_left (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-58, -61]) (countLit q [-62, -63]) (count1593 q) 1 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-58, -61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1594)) (countLit q [-58, -61]) (countLit q [-62, -63]) (count1593 q) 1 1 (meaning1589 q) (meaning1591 q) (meaning1594 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1591 = false ∨ valuation q 1594 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-58, -61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1595)) (countLit q [-58, -61]) (countLit q [-62, -63]) (count1593 q) 1 2 (meaning1589 q) (meaning1592 q) (meaning1595 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1592 = false ∨ valuation q 1595 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-58, -61]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-62, -63])
  have hm := merge_left (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-58, -61]) (countLit q [-62, -63]) (count1593 q) 2 (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1594 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1597 = true := by
  have hs : count1597 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1597)) (countLit q [-67]) (countLit q [-69]) (count1597 q) 1 (meaningNeg69 q) (meaning1597 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1597 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1597 = true := by
  have hs : count1597 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1597)) (countLit q [-67]) (countLit q [-69]) (count1597 q) 1 (meaningNeg67 q) (meaning1597 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1597 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1598 = true := by
  have hs : count1597 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1598)) (countLit q [-67]) (countLit q [-69]) (count1597 q) 1 1 (meaningNeg67 q) (meaningNeg69 q) (meaning1598 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 69 = true ∨ valuation q 1598 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1599 = true := by
  have hs : count1599 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1599)) (countLit q [-70]) (countLit q [-72]) (count1599 q) 1 (meaningNeg72 q) (meaning1599 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1599 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E024.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112024
