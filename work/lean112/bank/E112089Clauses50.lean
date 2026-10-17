import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1640)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 8 5 (meaning1556 q) (meaning1616 q) (meaning1640 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1616 = false ∨ valuation q 1640 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1641)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 8 6 (meaning1556 q) (meaning1617 q) (meaning1641 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1617 = false ∨ valuation q 1641 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1642)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 8 7 (meaning1556 q) (meaning1618 q) (meaning1642 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1618 = false ∨ valuation q 1642 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1639)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 9 3 (meaning1557 q) (meaning1614 q) (meaning1639 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1614 = false ∨ valuation q 1639 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1641)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 9 5 (meaning1557 q) (meaning1616 q) (meaning1641 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1616 = false ∨ valuation q 1641 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1650)) (countLit q [-64]) (countLit q [-66]) (count1650 q) 1 (meaningNeg66 q) (meaning1650 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1650 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1650)) (countLit q [-64]) (countLit q [-66]) (count1650 q) 1 (meaningNeg64 q) (meaning1650 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1650 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1651)) (countLit q [-64]) (countLit q [-66]) (count1650 q) 1 1 (meaningNeg64 q) (meaningNeg66 q) (meaning1651 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 1651 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1652)) (countLit q [-62]) (countLit q [-64, -66]) (count1652 q) 1 (meaning1650 q) (meaning1652 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1652 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1651)) (literal (valuationOf q) (1653)) (countLit q [-62]) (countLit q [-64, -66]) (count1652 q) 2 (meaning1651 q) (meaning1653 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1653 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1652)) (countLit q [-62]) (countLit q [-64, -66]) (count1652 q) 1 (meaningNeg62 q) (meaning1652 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1652 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1653)) (countLit q [-62]) (countLit q [-64, -66]) (count1652 q) 1 1 (meaningNeg62 q) (meaning1650 q) (meaning1653 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1650 = false ∨ valuation q 1653 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1651 = false ∨ valuationOf q 1654 = true := by
  have hs : count1652 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1654)) (countLit q [-62]) (countLit q [-64, -66]) (count1652 q) 1 2 (meaningNeg62 q) (meaning1651 q) (meaning1654 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1651 = false ∨ valuation q 1654 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1655)) (countLit q [-67]) (countLit q [-69]) (count1655 q) 1 (meaningNeg69 q) (meaning1655 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1655 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1655)) (countLit q [-67]) (countLit q [-69]) (count1655 q) 1 (meaningNeg67 q) (meaning1655 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1655 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1656)) (countLit q [-67]) (countLit q [-69]) (count1655 q) 1 1 (meaningNeg67 q) (meaningNeg69 q) (meaning1656 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 69 = true ∨ valuation q 1656 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1657)) (countLit q [-72]) (countLit q [-73]) (count1657 q) 1 (meaningNeg73 q) (meaning1657 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1657 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1657)) (countLit q [-72]) (countLit q [-73]) (count1657 q) 1 (meaningNeg72 q) (meaning1657 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1657 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1658)) (countLit q [-72]) (countLit q [-73]) (count1657 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1658 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1658 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-67, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1659)) (countLit q [-67, -69]) (countLit q [-72, -73]) (count1659 q) 1 (meaning1657 q) (meaning1659 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1659 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-67, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (1658)) (literal (valuationOf q) (1660)) (countLit q [-67, -69]) (countLit q [-72, -73]) (count1659 q) 2 (meaning1658 q) (meaning1660 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1660 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-67, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-72, -73])
  have hm := merge_left (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-67, -69]) (countLit q [-72, -73]) (count1659 q) 1 (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-67, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1660)) (countLit q [-67, -69]) (countLit q [-72, -73]) (count1659 q) 1 1 (meaning1655 q) (meaning1657 q) (meaning1660 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1657 = false ∨ valuation q 1660 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-67, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1661)) (countLit q [-67, -69]) (countLit q [-72, -73]) (count1659 q) 1 2 (meaning1655 q) (meaning1658 q) (meaning1661 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1658 = false ∨ valuation q 1661 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-67, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-72, -73])
  have hm := merge_left (literal (valuationOf q) (1656)) (literal (valuationOf q) (1660)) (countLit q [-67, -69]) (countLit q [-72, -73]) (count1659 q) 2 (meaning1656 q) (meaning1660 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1660 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-67, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1661)) (countLit q [-67, -69]) (countLit q [-72, -73]) (count1659 q) 2 1 (meaning1656 q) (meaning1657 q) (meaning1661 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1657 = false ∨ valuation q 1661 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-67, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1662)) (countLit q [-67, -69]) (countLit q [-72, -73]) (count1659 q) 2 2 (meaning1656 q) (meaning1658 q) (meaning1662 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1658 = false ∨ valuation q 1662 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1659)) (literal (valuationOf q) (1663)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 1 (meaning1659 q) (meaning1663 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1663 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1660)) (literal (valuationOf q) (1664)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 2 (meaning1660 q) (meaning1664 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1664 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1661)) (literal (valuationOf q) (1665)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 3 (meaning1661 q) (meaning1665 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1665 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1662)) (literal (valuationOf q) (1666)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 4 (meaning1662 q) (meaning1666 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1666 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1652)) (literal (valuationOf q) (1663)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 1 (meaning1652 q) (meaning1663 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1663 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E089.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112089
