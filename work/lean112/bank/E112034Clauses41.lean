import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1663)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 4 3 (meaning1623 q) (meaning1650 q) (meaning1663 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1650 = false ∨ valuation q 1663 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1664 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1664)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 4 4 (meaning1623 q) (meaning1651 q) (meaning1664 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1651 = false ∨ valuation q 1664 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1665 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1665)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 4 5 (meaning1623 q) (meaning1652 q) (meaning1665 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1652 = false ∨ valuation q 1665 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1666 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1666)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 4 6 (meaning1623 q) (meaning1653 q) (meaning1666 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1653 = false ∨ valuation q 1666 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1662 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1662)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 5 1 (meaning1624 q) (meaning1648 q) (meaning1662 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1648 = false ∨ valuation q 1662 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1663 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1663)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 5 2 (meaning1624 q) (meaning1649 q) (meaning1663 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1649 = false ∨ valuation q 1663 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1664 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1664)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 5 3 (meaning1624 q) (meaning1650 q) (meaning1664 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1650 = false ∨ valuation q 1664 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1665 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1665)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 5 4 (meaning1624 q) (meaning1651 q) (meaning1665 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1651 = false ∨ valuation q 1665 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1664 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1664)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 6 2 (meaning1625 q) (meaning1649 q) (meaning1664 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1649 = false ∨ valuation q 1664 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1665 = true := by
  have hs : count1657 q = (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) + (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -35, -36, -37, -40, -42]) (l₂ := [-44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1665)) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42]) (countLit q [-44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1657 q) 6 3 (meaning1625 q) (meaning1650 q) (meaning1665 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1650 = false ∨ valuation q 1665 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1685 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1685)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 5 7 (meaning1592 q) (meaning1663 q) (meaning1685 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1663 = false ∨ valuation q 1685 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1686 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1686)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 5 8 (meaning1592 q) (meaning1664 q) (meaning1686 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1664 = false ∨ valuation q 1686 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1682 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1682)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 6 3 (meaning1593 q) (meaning1659 q) (meaning1682 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1659 = false ∨ valuation q 1682 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1683 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1683)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 6 4 (meaning1593 q) (meaning1660 q) (meaning1683 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1660 = false ∨ valuation q 1683 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1684 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1684)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 6 5 (meaning1593 q) (meaning1661 q) (meaning1684 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1661 = false ∨ valuation q 1684 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1685 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1685)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 6 6 (meaning1593 q) (meaning1662 q) (meaning1685 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1662 = false ∨ valuation q 1685 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1686 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1686)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 6 7 (meaning1593 q) (meaning1663 q) (meaning1686 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1663 = false ∨ valuation q 1686 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1687 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1687)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 6 8 (meaning1593 q) (meaning1664 q) (meaning1687 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1664 = false ∨ valuation q 1687 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1688 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1688)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 6 9 (meaning1593 q) (meaning1665 q) (meaning1688 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1665 = false ∨ valuation q 1688 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1689 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1689)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 6 10 (meaning1593 q) (meaning1666 q) (meaning1689 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1666 = false ∨ valuation q 1689 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1682 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1682)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 2 (meaning1594 q) (meaning1658 q) (meaning1682 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1658 = false ∨ valuation q 1682 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1683 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1683)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 3 (meaning1594 q) (meaning1659 q) (meaning1683 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1659 = false ∨ valuation q 1683 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1684 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1684)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 4 (meaning1594 q) (meaning1660 q) (meaning1684 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1660 = false ∨ valuation q 1684 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1685 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1685)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 5 (meaning1594 q) (meaning1661 q) (meaning1685 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1661 = false ∨ valuation q 1685 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1686 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1686)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 6 (meaning1594 q) (meaning1662 q) (meaning1686 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1662 = false ∨ valuation q 1686 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1687 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1687)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 7 (meaning1594 q) (meaning1663 q) (meaning1687 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1663 = false ∨ valuation q 1687 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1688 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1688)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 8 (meaning1594 q) (meaning1664 q) (meaning1688 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1664 = false ∨ valuation q 1688 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1689 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1689)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 9 (meaning1594 q) (meaning1665 q) (meaning1689 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1665 = false ∨ valuation q 1689 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1690 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 7 10 (meaning1594 q) (meaning1666 q) (meaning1690 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1666 = false ∨ valuation q 1690 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1684 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1684)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 8 3 (meaning1595 q) (meaning1659 q) (meaning1684 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1659 = false ∨ valuation q 1684 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1685 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1685)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 8 4 (meaning1595 q) (meaning1660 q) (meaning1685 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1660 = false ∨ valuation q 1685 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1686 = true := by
  have hs : count1674 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) + (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (l₂ := [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1686)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]) (countLit q [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]) (count1674 q) 8 5 (meaning1595 q) (meaning1661 q) (meaning1686 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1661 = false ∨ valuation q 1686 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E034.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112034
