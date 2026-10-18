import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1637)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 6 (meaning1552 q) (meaning1617 q) (meaning1637 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1617 = false ∨ valuation q 1637 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1638)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 7 (meaning1552 q) (meaning1618 q) (meaning1638 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1618 = false ∨ valuation q 1638 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1639)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 8 (meaning1552 q) (meaning1619 q) (meaning1639 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1619 = false ∨ valuation q 1639 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1640)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 9 (meaning1552 q) (meaning1620 q) (meaning1640 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1620 = false ∨ valuation q 1640 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1641)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 10 (meaning1552 q) (meaning1621 q) (meaning1641 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1621 = false ∨ valuation q 1641 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1634 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1634)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 2 (meaning1553 q) (meaning1613 q) (meaning1634 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1613 = false ∨ valuation q 1634 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1635 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1635)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 3 (meaning1553 q) (meaning1614 q) (meaning1635 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1614 = false ∨ valuation q 1635 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1636 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1636)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 4 (meaning1553 q) (meaning1615 q) (meaning1636 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1615 = false ∨ valuation q 1636 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1637)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 5 (meaning1553 q) (meaning1616 q) (meaning1637 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1616 = false ∨ valuation q 1637 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1638)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 6 (meaning1553 q) (meaning1617 q) (meaning1638 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1617 = false ∨ valuation q 1638 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1639)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 7 (meaning1553 q) (meaning1618 q) (meaning1639 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1618 = false ∨ valuation q 1639 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1640)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 8 (meaning1553 q) (meaning1619 q) (meaning1640 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1619 = false ∨ valuation q 1640 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1641)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 9 (meaning1553 q) (meaning1620 q) (meaning1641 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1620 = false ∨ valuation q 1641 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1642)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 5 10 (meaning1553 q) (meaning1621 q) (meaning1642 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1621 = false ∨ valuation q 1642 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1635 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1635)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 6 2 (meaning1554 q) (meaning1613 q) (meaning1635 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1613 = false ∨ valuation q 1635 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1636 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1636)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 6 3 (meaning1554 q) (meaning1614 q) (meaning1636 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1614 = false ∨ valuation q 1636 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1637)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 6 4 (meaning1554 q) (meaning1615 q) (meaning1637 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1615 = false ∨ valuation q 1637 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1638)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 6 5 (meaning1554 q) (meaning1616 q) (meaning1638 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1616 = false ∨ valuation q 1638 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1639)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 6 6 (meaning1554 q) (meaning1617 q) (meaning1639 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1617 = false ∨ valuation q 1639 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1640)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 6 7 (meaning1554 q) (meaning1618 q) (meaning1640 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1618 = false ∨ valuation q 1640 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1641)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 6 8 (meaning1554 q) (meaning1619 q) (meaning1641 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1619 = false ∨ valuation q 1641 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1642)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 6 9 (meaning1554 q) (meaning1620 q) (meaning1642 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1620 = false ∨ valuation q 1642 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1636 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1636)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 7 2 (meaning1555 q) (meaning1613 q) (meaning1636 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1613 = false ∨ valuation q 1636 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1637)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 7 3 (meaning1555 q) (meaning1614 q) (meaning1637 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1614 = false ∨ valuation q 1637 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1638)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 7 4 (meaning1555 q) (meaning1615 q) (meaning1638 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1615 = false ∨ valuation q 1638 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1639)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 7 5 (meaning1555 q) (meaning1616 q) (meaning1639 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1616 = false ∨ valuation q 1639 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1640)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 7 6 (meaning1555 q) (meaning1617 q) (meaning1640 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1617 = false ∨ valuation q 1640 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1641)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 7 7 (meaning1555 q) (meaning1618 q) (meaning1641 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1618 = false ∨ valuation q 1641 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1642)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 7 8 (meaning1555 q) (meaning1619 q) (meaning1642 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1619 = false ∨ valuation q 1642 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1637)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 8 2 (meaning1556 q) (meaning1613 q) (meaning1637 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1613 = false ∨ valuation q 1637 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1638)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 8 3 (meaning1556 q) (meaning1614 q) (meaning1638 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1614 = false ∨ valuation q 1638 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1639)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 8 4 (meaning1556 q) (meaning1615 q) (meaning1639 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1615 = false ∨ valuation q 1639 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E089.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112089
