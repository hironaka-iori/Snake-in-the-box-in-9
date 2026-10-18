import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1624 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1624)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 7 4 (meaning1547 q) (meaning1602 q) (meaning1624 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1602 = false ∨ valuation q 1624 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1625 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1625)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 7 5 (meaning1547 q) (meaning1603 q) (meaning1625 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1603 = false ∨ valuation q 1625 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1626 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1626)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 7 6 (meaning1547 q) (meaning1604 q) (meaning1626 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1604 = false ∨ valuation q 1626 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1621 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_left (literal (valuationOf q) (1548)) (literal (valuationOf q) (1621)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 8 (meaning1548 q) (meaning1621 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1621 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1622 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1622)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 8 1 (meaning1548 q) (meaning1599 q) (meaning1622 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1599 = false ∨ valuation q 1622 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 8 2 (meaning1548 q) (meaning1600 q) (meaning1623 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1600 = false ∨ valuation q 1623 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1624 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1624)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 8 3 (meaning1548 q) (meaning1601 q) (meaning1624 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1601 = false ∨ valuation q 1624 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1625 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1625)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 8 4 (meaning1548 q) (meaning1602 q) (meaning1625 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1602 = false ∨ valuation q 1625 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1626 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1626)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 8 5 (meaning1548 q) (meaning1603 q) (meaning1626 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1603 = false ∨ valuation q 1626 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1623 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1623)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 9 1 (meaning1549 q) (meaning1599 q) (meaning1623 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1599 = false ∨ valuation q 1623 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1624 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1624)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 9 2 (meaning1549 q) (meaning1600 q) (meaning1624 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1600 = false ∨ valuation q 1624 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1625 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1625)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 9 3 (meaning1549 q) (meaning1601 q) (meaning1625 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1601 = false ∨ valuation q 1625 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1626 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1626)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 9 4 (meaning1549 q) (meaning1602 q) (meaning1626 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1602 = false ∨ valuation q 1626 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1624 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1624)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 10 1 (meaning1550 q) (meaning1599 q) (meaning1624 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1599 = false ∨ valuation q 1624 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1625 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1625)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 10 2 (meaning1550 q) (meaning1600 q) (meaning1625 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1600 = false ∨ valuation q 1625 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1626 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1626)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 10 3 (meaning1550 q) (meaning1601 q) (meaning1626 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1601 = false ∨ valuation q 1626 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1632)) (countLit q [-66]) (countLit q [-67]) (count1632 q) 1 (meaningNeg67 q) (meaning1632 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1632 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1632)) (countLit q [-66]) (countLit q [-67]) (count1632 q) 1 (meaningNeg66 q) (meaning1632 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1632 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1633)) (countLit q [-66]) (countLit q [-67]) (count1632 q) 1 1 (meaningNeg66 q) (meaningNeg67 q) (meaning1633 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 1633 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 1 (meaning1632 q) (meaning1634 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 2 (meaning1633 q) (meaning1635 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1634)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 1 (meaningNeg65 q) (meaning1634 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1634 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1635)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 1 1 (meaningNeg65 q) (meaning1632 q) (meaning1635 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1632 = false ∨ valuation q 1635 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-65]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1636)) (countLit q [-65]) (countLit q [-66, -67]) (count1634 q) 1 2 (meaningNeg65 q) (meaning1633 q) (meaning1636 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1633 = false ∨ valuation q 1636 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1637)) (countLit q [-69]) (countLit q [-73]) (count1637 q) 1 (meaningNeg73 q) (meaning1637 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1637 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1637)) (countLit q [-69]) (countLit q [-73]) (count1637 q) 1 (meaningNeg69 q) (meaning1637 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1637 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1638)) (countLit q [-69]) (countLit q [-73]) (count1637 q) 1 1 (meaningNeg69 q) (meaningNeg73 q) (meaning1638 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 73 = true ∨ valuation q 1638 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1639)) (countLit q [-77]) (countLit q [-78]) (count1639 q) 1 (meaningNeg78 q) (meaning1639 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1639 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1639)) (countLit q [-77]) (countLit q [-78]) (count1639 q) 1 (meaningNeg77 q) (meaning1639 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1639 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1640)) (countLit q [-77]) (countLit q [-78]) (count1639 q) 1 1 (meaningNeg77 q) (meaningNeg78 q) (meaning1640 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 78 = true ∨ valuation q 1640 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-69, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -73]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (countLit q [-69, -73]) (countLit q [-77, -78]) (count1641 q) 1 (meaning1639 q) (meaning1641 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-69, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -73]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (countLit q [-69, -73]) (countLit q [-77, -78]) (count1641 q) 2 (meaning1640 q) (meaning1642 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E258.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112258
