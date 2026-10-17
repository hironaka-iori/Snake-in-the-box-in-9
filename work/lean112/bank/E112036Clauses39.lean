import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1694 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1694)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 6 8 (meaning1600 q) (meaning1671 q) (meaning1694 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1671 = false ∨ valuation q 1694 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1695 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1695)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 6 9 (meaning1600 q) (meaning1672 q) (meaning1695 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1672 = false ∨ valuation q 1695 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1697 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1697)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 6 11 (meaning1600 q) (meaning1674 q) (meaning1697 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1674 = false ∨ valuation q 1697 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1691 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1691)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 7 4 (meaning1601 q) (meaning1667 q) (meaning1691 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1667 = false ∨ valuation q 1691 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1692 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1692)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 7 5 (meaning1601 q) (meaning1668 q) (meaning1692 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1668 = false ∨ valuation q 1692 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1693 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1693)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 7 6 (meaning1601 q) (meaning1669 q) (meaning1693 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1669 = false ∨ valuation q 1693 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1694 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1694)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 7 7 (meaning1601 q) (meaning1670 q) (meaning1694 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1670 = false ∨ valuation q 1694 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1695 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1695)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 7 8 (meaning1601 q) (meaning1671 q) (meaning1695 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1671 = false ∨ valuation q 1695 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1696 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1696)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 7 9 (meaning1601 q) (meaning1672 q) (meaning1696 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1672 = false ∨ valuation q 1696 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1697 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1697)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 7 10 (meaning1601 q) (meaning1673 q) (meaning1697 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1673 = false ∨ valuation q 1697 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1692 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1692)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 8 4 (meaning1602 q) (meaning1667 q) (meaning1692 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1667 = false ∨ valuation q 1692 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1693 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1693)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 8 5 (meaning1602 q) (meaning1668 q) (meaning1693 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1668 = false ∨ valuation q 1693 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1694 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1694)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 8 6 (meaning1602 q) (meaning1669 q) (meaning1694 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1669 = false ∨ valuation q 1694 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1695 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1695)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 8 7 (meaning1602 q) (meaning1670 q) (meaning1695 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1670 = false ∨ valuation q 1695 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1696 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1696)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 8 8 (meaning1602 q) (meaning1671 q) (meaning1696 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1671 = false ∨ valuation q 1696 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1697 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1697)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 8 9 (meaning1602 q) (meaning1672 q) (meaning1697 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1672 = false ∨ valuation q 1697 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1692 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1692)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 9 3 (meaning1603 q) (meaning1666 q) (meaning1692 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1666 = false ∨ valuation q 1692 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1693 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1693)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 9 4 (meaning1603 q) (meaning1667 q) (meaning1693 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1667 = false ∨ valuation q 1693 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1694 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1694)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 9 5 (meaning1603 q) (meaning1668 q) (meaning1694 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1668 = false ∨ valuation q 1694 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1695 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1695)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 9 6 (meaning1603 q) (meaning1669 q) (meaning1695 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1669 = false ∨ valuation q 1695 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1696 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1696)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 9 7 (meaning1603 q) (meaning1670 q) (meaning1696 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1670 = false ∨ valuation q 1696 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1694 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1694)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 10 4 (meaning1604 q) (meaning1667 q) (meaning1694 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1667 = false ∨ valuation q 1694 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1695 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1695)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 10 5 (meaning1604 q) (meaning1668 q) (meaning1695 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1668 = false ∨ valuation q 1695 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1696 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1696)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 10 6 (meaning1604 q) (meaning1669 q) (meaning1696 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1669 = false ∨ valuation q 1696 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1697 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1697)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 10 7 (meaning1604 q) (meaning1670 q) (meaning1697 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1670 = false ∨ valuation q 1697 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1694 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1694)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 11 3 (meaning1605 q) (meaning1666 q) (meaning1694 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1666 = false ∨ valuation q 1694 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1695 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1695)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 11 4 (meaning1605 q) (meaning1667 q) (meaning1695 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1667 = false ∨ valuation q 1695 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1696 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1696)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 11 5 (meaning1605 q) (meaning1668 q) (meaning1696 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1668 = false ∨ valuation q 1696 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1695 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1695)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 12 3 (meaning1606 q) (meaning1666 q) (meaning1695 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1666 = false ∨ valuation q 1695 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1696 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1696)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 12 4 (meaning1606 q) (meaning1667 q) (meaning1696 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1667 = false ∨ valuation q 1696 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1695 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1695)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 13 2 (meaning1607 q) (meaning1665 q) (meaning1695 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1665 = false ∨ valuation q 1695 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (1707)) (countLit q [-63]) (countLit q [-64]) (count1707 q) 1 (meaningNeg64 q) (meaning1707 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1707 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E036.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112036
