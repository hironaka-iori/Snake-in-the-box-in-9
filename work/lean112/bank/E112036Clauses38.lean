import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1669 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1669)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 2 4 (meaning1628 q) (meaning1658 q) (meaning1669 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1658 = false ∨ valuation q 1669 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1670 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1670)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 2 5 (meaning1628 q) (meaning1659 q) (meaning1670 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1659 = false ∨ valuation q 1670 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1671 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1671)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 2 6 (meaning1628 q) (meaning1660 q) (meaning1671 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1660 = false ∨ valuation q 1671 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1667 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1667)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 3 1 (meaning1629 q) (meaning1655 q) (meaning1667 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1655 = false ∨ valuation q 1667 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1668 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1668)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 3 2 (meaning1629 q) (meaning1656 q) (meaning1668 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1656 = false ∨ valuation q 1668 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1669 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1669)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 3 3 (meaning1629 q) (meaning1657 q) (meaning1669 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1657 = false ∨ valuation q 1669 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1670 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1670)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 3 4 (meaning1629 q) (meaning1658 q) (meaning1670 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1658 = false ∨ valuation q 1670 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1671 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1671)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 3 5 (meaning1629 q) (meaning1659 q) (meaning1671 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1659 = false ∨ valuation q 1671 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1672 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1672)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 3 6 (meaning1629 q) (meaning1660 q) (meaning1672 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1660 = false ∨ valuation q 1672 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1667 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_left (literal (valuationOf q) (1630)) (literal (valuationOf q) (1667)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 4 (meaning1630 q) (meaning1667 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1667 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1668 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1668)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 4 1 (meaning1630 q) (meaning1655 q) (meaning1668 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1655 = false ∨ valuation q 1668 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1669 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1669)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 4 2 (meaning1630 q) (meaning1656 q) (meaning1669 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1656 = false ∨ valuation q 1669 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1670 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1670)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 4 3 (meaning1630 q) (meaning1657 q) (meaning1670 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1657 = false ∨ valuation q 1670 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1671 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1671)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 4 4 (meaning1630 q) (meaning1658 q) (meaning1671 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1658 = false ∨ valuation q 1671 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1672 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1672)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 4 5 (meaning1630 q) (meaning1659 q) (meaning1672 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1659 = false ∨ valuation q 1672 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1673 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1673)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 4 6 (meaning1630 q) (meaning1660 q) (meaning1673 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1660 = false ∨ valuation q 1673 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1669 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1669)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 5 1 (meaning1631 q) (meaning1655 q) (meaning1669 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1655 = false ∨ valuation q 1669 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1670 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1670)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 5 2 (meaning1631 q) (meaning1656 q) (meaning1670 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1656 = false ∨ valuation q 1670 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1671 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1671)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 5 3 (meaning1631 q) (meaning1657 q) (meaning1671 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1657 = false ∨ valuation q 1671 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1672 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1672)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 5 4 (meaning1631 q) (meaning1658 q) (meaning1672 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1658 = false ∨ valuation q 1672 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1673 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1673)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 5 5 (meaning1631 q) (meaning1659 q) (meaning1673 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1659 = false ∨ valuation q 1673 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1674 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1674)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 5 6 (meaning1631 q) (meaning1660 q) (meaning1674 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1660 = false ∨ valuation q 1674 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1670 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1670)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 6 1 (meaning1632 q) (meaning1655 q) (meaning1670 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1655 = false ∨ valuation q 1670 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1671 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1671)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 6 2 (meaning1632 q) (meaning1656 q) (meaning1671 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1656 = false ∨ valuation q 1671 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1672 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1672)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 6 3 (meaning1632 q) (meaning1657 q) (meaning1672 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1657 = false ∨ valuation q 1672 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1673 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1673)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 6 4 (meaning1632 q) (meaning1658 q) (meaning1673 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1658 = false ∨ valuation q 1673 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1674 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1674)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 6 5 (meaning1632 q) (meaning1659 q) (meaning1674 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1659 = false ∨ valuation q 1674 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1692 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1692)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 5 7 (meaning1599 q) (meaning1670 q) (meaning1692 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1670 = false ∨ valuation q 1692 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1693 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1693)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 5 8 (meaning1599 q) (meaning1671 q) (meaning1693 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1671 = false ∨ valuation q 1693 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1691 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1691)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 6 5 (meaning1600 q) (meaning1668 q) (meaning1691 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1668 = false ∨ valuation q 1691 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1692 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1692)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 6 6 (meaning1600 q) (meaning1669 q) (meaning1692 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1669 = false ∨ valuation q 1692 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1693 = true := by
  have hs : count1681 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) + (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (l₂ := [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1693)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16, -17, -19, -21, -23, -25, -26, -27, -28]) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45, -47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1681 q) 6 7 (meaning1600 q) (meaning1670 q) (meaning1693 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1670 = false ∨ valuation q 1693 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E036.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112036
