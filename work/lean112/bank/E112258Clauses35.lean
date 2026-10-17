import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1618 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1618)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 2 3 (meaning1542 q) (meaning1601 q) (meaning1618 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1601 = false ∨ valuation q 1618 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 2 4 (meaning1542 q) (meaning1602 q) (meaning1619 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1602 = false ∨ valuation q 1619 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 2 5 (meaning1542 q) (meaning1603 q) (meaning1620 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1603 = false ∨ valuation q 1620 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 2 6 (meaning1542 q) (meaning1604 q) (meaning1621 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1604 = false ∨ valuation q 1621 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1618 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1618)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 3 2 (meaning1543 q) (meaning1600 q) (meaning1618 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1600 = false ∨ valuation q 1618 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 3 3 (meaning1543 q) (meaning1601 q) (meaning1619 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1601 = false ∨ valuation q 1619 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 3 4 (meaning1543 q) (meaning1602 q) (meaning1620 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1602 = false ∨ valuation q 1620 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 3 5 (meaning1543 q) (meaning1603 q) (meaning1621 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1603 = false ∨ valuation q 1621 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 3 6 (meaning1543 q) (meaning1604 q) (meaning1622 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1604 = false ∨ valuation q 1622 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 3 7 (meaning1543 q) (meaning1605 q) (meaning1623 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1605 = false ∨ valuation q 1623 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1618 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1618)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 4 1 (meaning1544 q) (meaning1599 q) (meaning1618 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1599 = false ∨ valuation q 1618 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 4 2 (meaning1544 q) (meaning1600 q) (meaning1619 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1600 = false ∨ valuation q 1619 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 4 3 (meaning1544 q) (meaning1601 q) (meaning1620 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1601 = false ∨ valuation q 1620 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 4 4 (meaning1544 q) (meaning1602 q) (meaning1621 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1602 = false ∨ valuation q 1621 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 4 5 (meaning1544 q) (meaning1603 q) (meaning1622 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1603 = false ∨ valuation q 1622 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 4 6 (meaning1544 q) (meaning1604 q) (meaning1623 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1604 = false ∨ valuation q 1623 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 5 1 (meaning1545 q) (meaning1599 q) (meaning1619 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1599 = false ∨ valuation q 1619 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 5 2 (meaning1545 q) (meaning1600 q) (meaning1620 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1600 = false ∨ valuation q 1620 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 5 3 (meaning1545 q) (meaning1601 q) (meaning1621 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1601 = false ∨ valuation q 1621 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 5 4 (meaning1545 q) (meaning1602 q) (meaning1622 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1602 = false ∨ valuation q 1622 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 5 5 (meaning1545 q) (meaning1603 q) (meaning1623 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1603 = false ∨ valuation q 1623 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1624 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1624)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 5 6 (meaning1545 q) (meaning1604 q) (meaning1624 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1604 = false ∨ valuation q 1624 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1625 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1625)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 5 7 (meaning1545 q) (meaning1605 q) (meaning1625 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1605 = false ∨ valuation q 1625 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 6 1 (meaning1546 q) (meaning1599 q) (meaning1620 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1599 = false ∨ valuation q 1620 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 6 2 (meaning1546 q) (meaning1600 q) (meaning1621 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1600 = false ∨ valuation q 1621 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 6 3 (meaning1546 q) (meaning1601 q) (meaning1622 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1601 = false ∨ valuation q 1622 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 6 4 (meaning1546 q) (meaning1602 q) (meaning1623 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1602 = false ∨ valuation q 1623 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1624 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1624)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 6 5 (meaning1546 q) (meaning1603 q) (meaning1624 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1603 = false ∨ valuation q 1624 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1625 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1625)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 6 6 (meaning1546 q) (meaning1604 q) (meaning1625 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1604 = false ∨ valuation q 1625 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 7 1 (meaning1547 q) (meaning1599 q) (meaning1621 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1599 = false ∨ valuation q 1621 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 7 2 (meaning1547 q) (meaning1600 q) (meaning1622 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1600 = false ∨ valuation q 1622 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 7 3 (meaning1547 q) (meaning1601 q) (meaning1623 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1601 = false ∨ valuation q 1623 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E258.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112258
