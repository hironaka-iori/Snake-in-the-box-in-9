import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1688 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1688)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 1 2 (meaning1674 q) (meaning1683 q) (meaning1688 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1683 = false ∨ valuation q 1688 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1689 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1689)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 1 3 (meaning1674 q) (meaning1684 q) (meaning1689 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1684 = false ∨ valuation q 1689 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1675)) (literal (valuationOf q) (1687)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 2 (meaning1675 q) (meaning1687 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1687 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1688)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 2 1 (meaning1675 q) (meaning1682 q) (meaning1688 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1682 = false ∨ valuation q 1688 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1689 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1689)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 2 2 (meaning1675 q) (meaning1683 q) (meaning1689 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1683 = false ∨ valuation q 1689 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1690 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1690)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 2 3 (meaning1675 q) (meaning1684 q) (meaning1690 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1684 = false ∨ valuation q 1690 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1691 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1691)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 2 4 (meaning1675 q) (meaning1685 q) (meaning1691 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1685 = false ∨ valuation q 1691 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1690 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1690)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 3 2 (meaning1676 q) (meaning1683 q) (meaning1690 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1683 = false ∨ valuation q 1690 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 1 3 (meaning1663 q) (meaning1688 q) (meaning1697 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1688 = false ∨ valuation q 1697 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 1 4 (meaning1663 q) (meaning1689 q) (meaning1698 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1689 = false ∨ valuation q 1698 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1695 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1664)) (literal (valuationOf q) (1695)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 2 (meaning1664 q) (meaning1695 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1695 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1696)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 2 1 (meaning1664 q) (meaning1686 q) (meaning1696 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1686 = false ∨ valuation q 1696 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 2 2 (meaning1664 q) (meaning1687 q) (meaning1697 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1687 = false ∨ valuation q 1697 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 2 3 (meaning1664 q) (meaning1688 q) (meaning1698 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1688 = false ∨ valuation q 1698 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 2 4 (meaning1664 q) (meaning1689 q) (meaning1699 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1689 = false ∨ valuation q 1699 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1700)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 2 5 (meaning1664 q) (meaning1690 q) (meaning1700 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1690 = false ∨ valuation q 1700 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1701)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 2 6 (meaning1664 q) (meaning1691 q) (meaning1701 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1691 = false ∨ valuation q 1701 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1696 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1665)) (literal (valuationOf q) (1696)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 3 (meaning1665 q) (meaning1696 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1696 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 3 1 (meaning1665 q) (meaning1686 q) (meaning1697 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1686 = false ∨ valuation q 1697 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 3 2 (meaning1665 q) (meaning1687 q) (meaning1698 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1687 = false ∨ valuation q 1698 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 3 3 (meaning1665 q) (meaning1688 q) (meaning1699 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1688 = false ∨ valuation q 1699 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1700)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 3 4 (meaning1665 q) (meaning1689 q) (meaning1700 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1689 = false ∨ valuation q 1700 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1665)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1701)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 3 5 (meaning1665 q) (meaning1690 q) (meaning1701 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1690 = false ∨ valuation q 1701 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1666)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 4 (meaning1666 q) (meaning1697 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1697 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 4 1 (meaning1666 q) (meaning1686 q) (meaning1698 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1686 = false ∨ valuation q 1698 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 4 2 (meaning1666 q) (meaning1687 q) (meaning1699 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1687 = false ∨ valuation q 1699 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1700)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 4 3 (meaning1666 q) (meaning1688 q) (meaning1700 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1688 = false ∨ valuation q 1700 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1701 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1701)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 4 4 (meaning1666 q) (meaning1689 q) (meaning1701 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1689 = false ∨ valuation q 1701 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1702 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1666)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1702)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 4 5 (meaning1666 q) (meaning1690 q) (meaning1702 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1690 = false ∨ valuation q 1702 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1698 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1667)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 5 (meaning1667 q) (meaning1698 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1698 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1699 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 5 1 (meaning1667 q) (meaning1686 q) (meaning1699 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1686 = false ∨ valuation q 1699 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1700 = true := by
  have hs : count1694 q = (countLit q [-60, -62, -63, -65, -66, -68, -71]) + (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71]) (l₂ := [-73, -74, -77, -80, -82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1700)) (countLit q [-60, -62, -63, -65, -66, -68, -71]) (countLit q [-73, -74, -77, -80, -82, -83, -86, -89]) (count1694 q) 5 2 (meaning1667 q) (meaning1687 q) (meaning1700 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1687 = false ∨ valuation q 1700 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E008.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112008
