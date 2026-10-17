import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1652 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1652)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 2 1 (meaning1644 q) (meaning1647 q) (meaning1652 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1647 = false ∨ valuation q 1652 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1653 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1653)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 2 2 (meaning1644 q) (meaning1648 q) (meaning1653 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = false ∨ valuation q 1653 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1655)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 1 (meaning1650 q) (meaning1655 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1655 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1651)) (literal (valuationOf q) (1656)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 2 (meaning1651 q) (meaning1656 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1656 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1657)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 3 (meaning1652 q) (meaning1657 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1657 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1658)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 4 (meaning1653 q) (meaning1658 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1658 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1656)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 1 1 (meaning1639 q) (meaning1650 q) (meaning1656 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1650 = false ∨ valuation q 1656 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1657)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 1 2 (meaning1639 q) (meaning1651 q) (meaning1657 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1651 = false ∨ valuation q 1657 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1658)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 1 3 (meaning1639 q) (meaning1652 q) (meaning1658 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1652 = false ∨ valuation q 1658 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1659)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 1 4 (meaning1639 q) (meaning1653 q) (meaning1659 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1653 = false ∨ valuation q 1659 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_left (literal (valuationOf q) (1640)) (literal (valuationOf q) (1656)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 2 (meaning1640 q) (meaning1656 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1656 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1657)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 2 1 (meaning1640 q) (meaning1650 q) (meaning1657 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1650 = false ∨ valuation q 1657 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1658)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 2 2 (meaning1640 q) (meaning1651 q) (meaning1658 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1651 = false ∨ valuation q 1658 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1659)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 2 3 (meaning1640 q) (meaning1652 q) (meaning1659 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1652 = false ∨ valuation q 1659 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1660)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 2 4 (meaning1640 q) (meaning1653 q) (meaning1660 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1653 = false ∨ valuation q 1660 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1658)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 3 1 (meaning1641 q) (meaning1650 q) (meaning1658 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1650 = false ∨ valuation q 1658 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1659)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 3 2 (meaning1641 q) (meaning1651 q) (meaning1659 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1651 = false ∨ valuation q 1659 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1660)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 3 3 (meaning1641 q) (meaning1652 q) (meaning1660 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1652 = false ∨ valuation q 1660 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1659)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 4 1 (meaning1642 q) (meaning1650 q) (meaning1659 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1650 = false ∨ valuation q 1659 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-47, -50, -52, -54]) + (countLit q [-55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -52, -54]) (l₂ := [-55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1660)) (countLit q [-47, -50, -52, -54]) (countLit q [-55, -56, -57, -59, -61]) (count1655 q) 4 2 (meaning1642 q) (meaning1651 q) (meaning1660 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1651 = false ∨ valuation q 1660 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1656)) (literal (valuationOf q) (1665)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 2 (meaning1656 q) (meaning1665 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1665 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1666 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1666)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 3 (meaning1657 q) (meaning1666 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1666 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1667 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1658)) (literal (valuationOf q) (1667)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 4 (meaning1658 q) (meaning1667 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1667 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1665)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 1 1 (meaning1627 q) (meaning1655 q) (meaning1665 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1655 = false ∨ valuation q 1665 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1666 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1666)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 1 2 (meaning1627 q) (meaning1656 q) (meaning1666 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1656 = false ∨ valuation q 1666 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1667 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1667)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 1 3 (meaning1627 q) (meaning1657 q) (meaning1667 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1657 = false ∨ valuation q 1667 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1668 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1668)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 1 4 (meaning1627 q) (meaning1658 q) (meaning1668 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1658 = false ∨ valuation q 1668 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1669 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1669)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 1 5 (meaning1627 q) (meaning1659 q) (meaning1669 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1659 = false ∨ valuation q 1669 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1670 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1670)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 1 6 (meaning1627 q) (meaning1660 q) (meaning1670 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1660 = false ∨ valuation q 1670 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1666 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1666)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 2 1 (meaning1628 q) (meaning1655 q) (meaning1666 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1655 = false ∨ valuation q 1666 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1667 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1667)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 2 2 (meaning1628 q) (meaning1656 q) (meaning1667 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1656 = false ∨ valuation q 1667 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1668 = true := by
  have hs : count1664 q = (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) + (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -33, -37, -38, -39, -41, -44, -45]) (l₂ := [-47, -50, -52, -54, -55, -56, -57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1668)) (countLit q [-32, -33, -37, -38, -39, -41, -44, -45]) (countLit q [-47, -50, -52, -54, -55, -56, -57, -59, -61]) (count1664 q) 2 3 (meaning1628 q) (meaning1657 q) (meaning1668 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1657 = false ∨ valuation q 1668 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E036.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112036
