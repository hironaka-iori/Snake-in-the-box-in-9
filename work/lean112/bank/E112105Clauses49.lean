import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1680 = true := by
  have hs : count1680 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1680)) (countLit q [-88]) (countLit q [-89]) (count1680 q) 1 (meaningNeg89 q) (meaning1680 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1680 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1680 = true := by
  have hs : count1680 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1680)) (countLit q [-88]) (countLit q [-89]) (count1680 q) 1 (meaningNeg88 q) (meaning1680 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1680 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1681 = true := by
  have hs : count1680 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1681)) (countLit q [-88]) (countLit q [-89]) (count1680 q) 1 1 (meaningNeg88 q) (meaningNeg89 q) (meaning1681 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 89 = true ∨ valuation q 1681 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1682 = true := by
  have hs : count1682 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1682)) (countLit q [-91]) (countLit q [-93]) (count1682 q) 1 (meaningNeg93 q) (meaning1682 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1682 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1682 = true := by
  have hs : count1682 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1682)) (countLit q [-91]) (countLit q [-93]) (count1682 q) 1 (meaningNeg91 q) (meaning1682 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1682 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1683 = true := by
  have hs : count1682 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1683)) (countLit q [-91]) (countLit q [-93]) (count1682 q) 1 1 (meaningNeg91 q) (meaningNeg93 q) (meaning1683 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 1683 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1684 = true := by
  have hs : count1684 q = (countLit q [-88, -89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-91, -93])
  have hm := merge_right (literal (valuationOf q) (1682)) (literal (valuationOf q) (1684)) (countLit q [-88, -89]) (countLit q [-91, -93]) (count1684 q) 1 (meaning1682 q) (meaning1684 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1684 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1685 = true := by
  have hs : count1684 q = (countLit q [-88, -89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-91, -93])
  have hm := merge_right (literal (valuationOf q) (1683)) (literal (valuationOf q) (1685)) (countLit q [-88, -89]) (countLit q [-91, -93]) (count1684 q) 2 (meaning1683 q) (meaning1685 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1685 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1684 = true := by
  have hs : count1684 q = (countLit q [-88, -89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-91, -93])
  have hm := merge_left (literal (valuationOf q) (1680)) (literal (valuationOf q) (1684)) (countLit q [-88, -89]) (countLit q [-91, -93]) (count1684 q) 1 (meaning1680 q) (meaning1684 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1684 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1685 = true := by
  have hs : count1684 q = (countLit q [-88, -89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1685)) (countLit q [-88, -89]) (countLit q [-91, -93]) (count1684 q) 1 1 (meaning1680 q) (meaning1682 q) (meaning1685 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1682 = false ∨ valuation q 1685 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1686 = true := by
  have hs : count1684 q = (countLit q [-88, -89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1686)) (countLit q [-88, -89]) (countLit q [-91, -93]) (count1684 q) 1 2 (meaning1680 q) (meaning1683 q) (meaning1686 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1683 = false ∨ valuation q 1686 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1685 = true := by
  have hs : count1684 q = (countLit q [-88, -89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-91, -93])
  have hm := merge_left (literal (valuationOf q) (1681)) (literal (valuationOf q) (1685)) (countLit q [-88, -89]) (countLit q [-91, -93]) (count1684 q) 2 (meaning1681 q) (meaning1685 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1685 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1686 = true := by
  have hs : count1684 q = (countLit q [-88, -89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1686)) (countLit q [-88, -89]) (countLit q [-91, -93]) (count1684 q) 2 1 (meaning1681 q) (meaning1682 q) (meaning1686 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1682 = false ∨ valuation q 1686 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1687 = true := by
  have hs : count1684 q = (countLit q [-88, -89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1687)) (countLit q [-88, -89]) (countLit q [-91, -93]) (count1684 q) 2 2 (meaning1681 q) (meaning1683 q) (meaning1687 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1683 = false ∨ valuation q 1687 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1688 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1684)) (literal (valuationOf q) (1688)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 1 (meaning1684 q) (meaning1688 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1688 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1689 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1685)) (literal (valuationOf q) (1689)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 2 (meaning1685 q) (meaning1689 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1689 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1690 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1686)) (literal (valuationOf q) (1690)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 3 (meaning1686 q) (meaning1690 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1690 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1691 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1687)) (literal (valuationOf q) (1691)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 4 (meaning1687 q) (meaning1691 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1691 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1688 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1676)) (literal (valuationOf q) (1688)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 1 (meaning1676 q) (meaning1688 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1688 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1689 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1689)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 1 1 (meaning1676 q) (meaning1684 q) (meaning1689 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1684 = false ∨ valuation q 1689 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1690 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1690)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 1 2 (meaning1676 q) (meaning1685 q) (meaning1690 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1685 = false ∨ valuation q 1690 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1691 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1691)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 1 3 (meaning1676 q) (meaning1686 q) (meaning1691 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1686 = false ∨ valuation q 1691 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1692 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1692)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 1 4 (meaning1676 q) (meaning1687 q) (meaning1692 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1687 = false ∨ valuation q 1692 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1689 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1677)) (literal (valuationOf q) (1689)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 2 (meaning1677 q) (meaning1689 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1689 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1690 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1690)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 2 1 (meaning1677 q) (meaning1684 q) (meaning1690 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1684 = false ∨ valuation q 1690 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1691 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1691)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 2 2 (meaning1677 q) (meaning1685 q) (meaning1691 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1685 = false ∨ valuation q 1691 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1692 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1692)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 2 3 (meaning1677 q) (meaning1686 q) (meaning1692 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1686 = false ∨ valuation q 1692 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1693 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1693)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 2 4 (meaning1677 q) (meaning1687 q) (meaning1693 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1687 = false ∨ valuation q 1693 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1690 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1678)) (literal (valuationOf q) (1690)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 3 (meaning1678 q) (meaning1690 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1690 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1691 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1691)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 3 1 (meaning1678 q) (meaning1684 q) (meaning1691 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1684 = false ∨ valuation q 1691 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1692 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1692)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 3 2 (meaning1678 q) (meaning1685 q) (meaning1692 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1685 = false ∨ valuation q 1692 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1693 = true := by
  have hs : count1688 q = (countLit q [-78, -81, -83, -85]) + (countLit q [-88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85]) (l₂ := [-88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1693)) (countLit q [-78, -81, -83, -85]) (countLit q [-88, -89, -91, -93]) (count1688 q) 3 3 (meaning1678 q) (meaning1686 q) (meaning1693 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1686 = false ∨ valuation q 1693 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E105.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112105
