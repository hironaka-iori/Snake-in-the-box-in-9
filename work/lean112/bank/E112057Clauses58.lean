import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec58 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1857 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1581)) (countLit q [-27]) (countLit q [-29]) (count1581 q) 1 (meaningNeg29 q) (meaning1581 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1857 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1581 = true := counterClause1857 (baseVal q)

theorem counterClause1858 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1583 q) 1 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1858 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause1858 (baseVal q)

theorem counterClause1859 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1583 q) 1 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1859 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1859 (baseVal q)

theorem counterClause1860 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1583 q) 1 1 (meaning1579 q) (meaning1581 q) (meaning1584 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1860 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause1860 (baseVal q)

theorem counterClause1861 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-16, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1589)) (countLit q [-16, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count1587 q) 2 1 (meaning1576 q) (meaning1583 q) (meaning1589 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1861 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1583 = false ∨ valuation q 1589 = true := counterClause1861 (baseVal q)

theorem counterClause1862 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-16, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1590)) (countLit q [-16, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count1587 q) 2 2 (meaning1576 q) (meaning1584 q) (meaning1590 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1862 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1584 = false ∨ valuation q 1590 = true := counterClause1862 (baseVal q)

theorem counterClause1863 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1598)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1595 q) 1 3 (meaning1564 q) (meaning1589 q) (meaning1598 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1863 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1589 = false ∨ valuation q 1598 = true := counterClause1863 (baseVal q)

theorem counterClause1864 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1599)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1595 q) 2 3 (meaning1565 q) (meaning1589 q) (meaning1599 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1864 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1589 = false ∨ valuation q 1599 = true := counterClause1864 (baseVal q)

theorem counterClause1865 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1600)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1595 q) 2 4 (meaning1565 q) (meaning1590 q) (meaning1600 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1865 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1590 = false ∨ valuation q 1600 = true := counterClause1865 (baseVal q)

theorem counterClause1866 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (1610)) (countLit q [-31]) (countLit q [-32]) (count1610 q) 1 (meaningNeg32 q) (meaning1610 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1866 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1610 = true := counterClause1866 (baseVal q)

theorem counterClause1867 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1610)) (countLit q [-31]) (countLit q [-32]) (count1610 q) 1 (meaningNeg31 q) (meaning1610 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1867 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1610 = true := counterClause1867 (baseVal q)

theorem counterClause1868 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1612)) (countLit q [-34]) (countLit q [-37]) (count1612 q) 1 (meaningNeg37 q) (meaning1612 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1868 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1612 = true := counterClause1868 (baseVal q)

theorem counterClause1869 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1612)) (countLit q [-34]) (countLit q [-37]) (count1612 q) 1 (meaningNeg34 q) (meaning1612 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1869 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1612 = true := counterClause1869 (baseVal q)

theorem counterClause1870 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-31, -32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -37])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1614)) (countLit q [-31, -32]) (countLit q [-34, -37]) (count1614 q) 1 (meaning1612 q) (meaning1614 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1870 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1614 = true := counterClause1870 (baseVal q)

theorem counterClause1871 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-31, -32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -37])
  have hm := merge_left (literal (valuationOf q) (1610)) (literal (valuationOf q) (1614)) (countLit q [-31, -32]) (countLit q [-34, -37]) (count1614 q) 1 (meaning1610 q) (meaning1614 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1871 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1614 = true := counterClause1871 (baseVal q)

theorem counterClause1872 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1618)) (countLit q [-38]) (countLit q [-40]) (count1618 q) 1 (meaningNeg40 q) (meaning1618 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1872 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1618 = true := counterClause1872 (baseVal q)

theorem counterClause1873 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1618)) (countLit q [-38]) (countLit q [-40]) (count1618 q) 1 (meaningNeg38 q) (meaning1618 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1873 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1618 = true := counterClause1873 (baseVal q)

theorem counterClause1874 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-41]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1620)) (countLit q [-41]) (countLit q [-44]) (count1620 q) 1 (meaningNeg41 q) (meaning1620 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1874 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1620 = true := counterClause1874 (baseVal q)

theorem counterClause1875 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-41]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1621)) (countLit q [-41]) (countLit q [-44]) (count1620 q) 1 1 (meaningNeg41 q) (meaningNeg44 q) (meaning1621 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1875 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 44 = true ∨ valuation q 1621 = true := counterClause1875 (baseVal q)

theorem counterClause1876 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1622 = true := by
  have hs : count1622 q = (countLit q [-38, -40]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-41, -44])
  have hm := merge_right (literal (valuationOf q) (1620)) (literal (valuationOf q) (1622)) (countLit q [-38, -40]) (countLit q [-41, -44]) (count1622 q) 1 (meaning1620 q) (meaning1622 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1876 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1622 = true := counterClause1876 (baseVal q)

theorem counterClause1877 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1623 = true := by
  have hs : count1622 q = (countLit q [-38, -40]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-41, -44])
  have hm := merge_right (literal (valuationOf q) (1621)) (literal (valuationOf q) (1623)) (countLit q [-38, -40]) (countLit q [-41, -44]) (count1622 q) 2 (meaning1621 q) (meaning1623 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1877 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1623 = true := counterClause1877 (baseVal q)

theorem counterClause1878 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1622 q = (countLit q [-38, -40]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-41, -44])
  have hm := merge_left (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-38, -40]) (countLit q [-41, -44]) (count1622 q) 1 (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1878 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1622 = true := counterClause1878 (baseVal q)

theorem counterClause1879 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true := by
  have hs : count1626 q = (countLit q [-31, -32, -34, -37]) + (countLit q [-38, -40, -41, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37]) (l₂ := [-38, -40, -41, -44])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1627)) (countLit q [-31, -32, -34, -37]) (countLit q [-38, -40, -41, -44]) (count1626 q) 1 1 (meaning1614 q) (meaning1622 q) (meaning1627 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1879 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1622 = false ∨ valuation q 1627 = true := counterClause1879 (baseVal q)

theorem counterClause1880 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1628 = true := by
  have hs : count1626 q = (countLit q [-31, -32, -34, -37]) + (countLit q [-38, -40, -41, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37]) (l₂ := [-38, -40, -41, -44])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1628)) (countLit q [-31, -32, -34, -37]) (countLit q [-38, -40, -41, -44]) (count1626 q) 1 2 (meaning1614 q) (meaning1623 q) (meaning1628 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1880 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1623 = false ∨ valuation q 1628 = true := counterClause1880 (baseVal q)

theorem counterClause1881 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1634)) (countLit q [-45]) (countLit q [-49]) (count1634 q) 1 (meaningNeg49 q) (meaning1634 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1881 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1634 = true := counterClause1881 (baseVal q)

theorem counterClause1882 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1634)) (countLit q [-45]) (countLit q [-49]) (count1634 q) 1 (meaningNeg45 q) (meaning1634 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1882 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1634 = true := counterClause1882 (baseVal q)

theorem counterClause1883 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1635)) (countLit q [-45]) (countLit q [-49]) (count1634 q) 1 1 (meaningNeg45 q) (meaningNeg49 q) (meaning1635 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1883 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 1635 = true := counterClause1883 (baseVal q)

theorem counterClause1884 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1636)) (countLit q [-52]) (countLit q [-53]) (count1636 q) 1 (meaningNeg53 q) (meaning1636 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1884 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1636 = true := counterClause1884 (baseVal q)

theorem counterClause1885 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1636)) (countLit q [-52]) (countLit q [-53]) (count1636 q) 1 (meaningNeg52 q) (meaning1636 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1885 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1636 = true := counterClause1885 (baseVal q)

theorem counterClause1886 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_right (literal (valuationOf q) (1636)) (literal (valuationOf q) (1638)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1638 q) 1 (meaning1636 q) (meaning1638 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1886 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1638 = true := counterClause1886 (baseVal q)

theorem counterClause1887 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1638)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1638 q) 1 (meaning1634 q) (meaning1638 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1887 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1638 = true := counterClause1887 (baseVal q)

theorem counterClause1888 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1636 = false ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1636)) (literal (valuationOf q) (1639)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1638 q) 1 1 (meaning1634 q) (meaning1636 q) (meaning1639 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1636 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1888 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1636 = false ∨ valuation q 1639 = true := counterClause1888 (baseVal q)

theorem block58 (q : Snake 81) (h : Conditions q) : B112E057.Block58 (valuation q) :=
  ⟨clause1857 q h, clause1858 q h, clause1859 q h, clause1860 q h, clause1861 q h, clause1862 q h, clause1863 q h, clause1864 q h, clause1865 q h, clause1866 q h, clause1867 q h, clause1868 q h, clause1869 q h, clause1870 q h, clause1871 q h, clause1872 q h, clause1873 q h, clause1874 q h, clause1875 q h, clause1876 q h, clause1877 q h, clause1878 q h, clause1879 q h, clause1880 q h, clause1881 q h, clause1882 q h, clause1883 q h, clause1884 q h, clause1885 q h, clause1886 q h, clause1887 q h, clause1888 q h⟩

end
end Snake9.Regrowth.E112057
