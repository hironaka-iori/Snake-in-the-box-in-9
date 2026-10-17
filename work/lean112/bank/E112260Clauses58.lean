import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec58 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1857 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1598 = true := by
  have hs : count1597 q = (countLit q [-33, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (1596)) (literal (valuationOf q) (1598)) (countLit q [-33, -35]) (countLit q [-37, -38]) (count1597 q) 2 (meaning1596 q) (meaning1598 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1857 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1598 = true := counterClause1857 (baseVal q)

theorem counterClause1858 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1597 = true := by
  have hs : count1597 q = (countLit q [-33, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -38])
  have hm := merge_left (literal (valuationOf q) (1593)) (literal (valuationOf q) (1597)) (countLit q [-33, -35]) (countLit q [-37, -38]) (count1597 q) 1 (meaning1593 q) (meaning1597 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1858 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1597 = true := counterClause1858 (baseVal q)

theorem counterClause1859 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1598 = true := by
  have hs : count1597 q = (countLit q [-33, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1598)) (countLit q [-33, -35]) (countLit q [-37, -38]) (count1597 q) 1 1 (meaning1593 q) (meaning1595 q) (meaning1598 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1859 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1595 = false ∨ valuation q 1598 = true := counterClause1859 (baseVal q)

theorem counterClause1860 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true := by
  have hs : count1597 q = (countLit q [-33, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1599)) (countLit q [-33, -35]) (countLit q [-37, -38]) (count1597 q) 1 2 (meaning1593 q) (meaning1596 q) (meaning1599 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1860 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1596 = false ∨ valuation q 1599 = true := counterClause1860 (baseVal q)

theorem counterClause1861 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1601)) (countLit q [-39]) (countLit q [-41]) (count1601 q) 1 (meaningNeg41 q) (meaning1601 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1861 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1601 = true := counterClause1861 (baseVal q)

theorem counterClause1862 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1601)) (countLit q [-39]) (countLit q [-41]) (count1601 q) 1 (meaningNeg39 q) (meaning1601 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1862 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1601 = true := counterClause1862 (baseVal q)

theorem counterClause1863 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1602 = true := by
  have hs : count1601 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1602)) (countLit q [-39]) (countLit q [-41]) (count1601 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning1602 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1863 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 1602 = true := counterClause1863 (baseVal q)

theorem counterClause1864 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1603)) (countLit q [-43]) (countLit q [-45]) (count1603 q) 1 (meaningNeg45 q) (meaning1603 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1864 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1603 = true := counterClause1864 (baseVal q)

theorem counterClause1865 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1603)) (countLit q [-43]) (countLit q [-45]) (count1603 q) 1 (meaningNeg43 q) (meaning1603 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1865 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1603 = true := counterClause1865 (baseVal q)

theorem counterClause1866 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1604 = true := by
  have hs : count1603 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1604)) (countLit q [-43]) (countLit q [-45]) (count1603 q) 1 1 (meaningNeg43 q) (meaningNeg45 q) (meaning1604 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1866 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 1604 = true := counterClause1866 (baseVal q)

theorem counterClause1867 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-39, -41]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -45])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (countLit q [-39, -41]) (countLit q [-43, -45]) (count1605 q) 1 (meaning1603 q) (meaning1605 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1867 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = true := counterClause1867 (baseVal q)

theorem counterClause1868 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-39, -41]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -45])
  have hm := merge_right (literal (valuationOf q) (1604)) (literal (valuationOf q) (1606)) (countLit q [-39, -41]) (countLit q [-43, -45]) (count1605 q) 2 (meaning1604 q) (meaning1606 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1868 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1606 = true := counterClause1868 (baseVal q)

theorem counterClause1869 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-39, -41]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -45])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-39, -41]) (countLit q [-43, -45]) (count1605 q) 1 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1869 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1869 (baseVal q)

theorem counterClause1870 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-39, -41]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (countLit q [-39, -41]) (countLit q [-43, -45]) (count1605 q) 1 1 (meaning1601 q) (meaning1603 q) (meaning1606 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1870 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1603 = false ∨ valuation q 1606 = true := counterClause1870 (baseVal q)

theorem counterClause1871 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-39, -41]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1607)) (countLit q [-39, -41]) (countLit q [-43, -45]) (count1605 q) 1 2 (meaning1601 q) (meaning1604 q) (meaning1607 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1871 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1604 = false ∨ valuation q 1607 = true := counterClause1871 (baseVal q)

theorem counterClause1872 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-39, -41]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -45])
  have hm := merge_left (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-39, -41]) (countLit q [-43, -45]) (count1605 q) 2 (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1872 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1606 = true := counterClause1872 (baseVal q)

theorem counterClause1873 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-39, -41]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-39, -41]) (countLit q [-43, -45]) (count1605 q) 2 1 (meaning1602 q) (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1873 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1603 = false ∨ valuation q 1607 = true := counterClause1873 (baseVal q)

theorem counterClause1874 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1608 = true := by
  have hs : count1605 q = (countLit q [-39, -41]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1608)) (countLit q [-39, -41]) (countLit q [-43, -45]) (count1605 q) 2 2 (meaning1602 q) (meaning1604 q) (meaning1608 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1874 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1604 = false ∨ valuation q 1608 = true := counterClause1874 (baseVal q)

theorem counterClause1875 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1609)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 1 (meaning1605 q) (meaning1609 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1875 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1609 = true := counterClause1875 (baseVal q)

theorem counterClause1876 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1610)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 2 (meaning1606 q) (meaning1610 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1876 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1610 = true := counterClause1876 (baseVal q)

theorem counterClause1877 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1611)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 3 (meaning1607 q) (meaning1611 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1877 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1611 = true := counterClause1877 (baseVal q)

theorem counterClause1878 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1609)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 1 (meaning1597 q) (meaning1609 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1878 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1609 = true := counterClause1878 (baseVal q)

theorem counterClause1879 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1610)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 1 1 (meaning1597 q) (meaning1605 q) (meaning1610 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1879 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1605 = false ∨ valuation q 1610 = true := counterClause1879 (baseVal q)

theorem counterClause1880 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1611)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 1 2 (meaning1597 q) (meaning1606 q) (meaning1611 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1880 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1606 = false ∨ valuation q 1611 = true := counterClause1880 (baseVal q)

theorem counterClause1881 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1612)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 1 3 (meaning1597 q) (meaning1607 q) (meaning1612 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1881 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1607 = false ∨ valuation q 1612 = true := counterClause1881 (baseVal q)

theorem counterClause1882 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1613)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 1 4 (meaning1597 q) (meaning1608 q) (meaning1613 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1882 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1608 = false ∨ valuation q 1613 = true := counterClause1882 (baseVal q)

theorem counterClause1883 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1610)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 2 (meaning1598 q) (meaning1610 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1883 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1610 = true := counterClause1883 (baseVal q)

theorem counterClause1884 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1611)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 2 1 (meaning1598 q) (meaning1605 q) (meaning1611 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1884 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1605 = false ∨ valuation q 1611 = true := counterClause1884 (baseVal q)

theorem counterClause1885 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1612)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 2 2 (meaning1598 q) (meaning1606 q) (meaning1612 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1885 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1606 = false ∨ valuation q 1612 = true := counterClause1885 (baseVal q)

theorem counterClause1886 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1613)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 2 3 (meaning1598 q) (meaning1607 q) (meaning1613 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1886 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1607 = false ∨ valuation q 1613 = true := counterClause1886 (baseVal q)

theorem counterClause1887 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1613 = true := by
  have hs : count1609 q = (countLit q [-33, -35, -37, -38]) + (countLit q [-39, -41, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -38]) (l₂ := [-39, -41, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1613)) (countLit q [-33, -35, -37, -38]) (countLit q [-39, -41, -43, -45]) (count1609 q) 3 2 (meaning1599 q) (meaning1606 q) (meaning1613 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1887 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1606 = false ∨ valuation q 1613 = true := counterClause1887 (baseVal q)

theorem counterClause1888 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-47]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1617)) (countLit q [-47]) (countLit q [-52]) (count1617 q) 1 (meaningNeg52 q) (meaning1617 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1888 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1617 = true := counterClause1888 (baseVal q)

theorem block58 (q : Snake 81) (h : Conditions q) : B112E260.Block58 (valuation q) :=
  ⟨clause1857 q h, clause1858 q h, clause1859 q h, clause1860 q h, clause1861 q h, clause1862 q h, clause1863 q h, clause1864 q h, clause1865 q h, clause1866 q h, clause1867 q h, clause1868 q h, clause1869 q h, clause1870 q h, clause1871 q h, clause1872 q h, clause1873 q h, clause1874 q h, clause1875 q h, clause1876 q h, clause1877 q h, clause1878 q h, clause1879 q h, clause1880 q h, clause1881 q h, clause1882 q h, clause1883 q h, clause1884 q h, clause1885 q h, clause1886 q h, clause1887 q h, clause1888 q h⟩

end
end Snake9.Regrowth.E112260
