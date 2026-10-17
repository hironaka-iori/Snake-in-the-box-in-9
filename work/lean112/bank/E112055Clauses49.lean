import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1729 = true := by
  have hs : count1729 q = (countLit q [-72, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -79])
  have hm := merge_left (literal (valuationOf q) (1725)) (literal (valuationOf q) (1729)) (countLit q [-72, -75]) (countLit q [-77, -79]) (count1729 q) 1 (meaning1725 q) (meaning1729 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1729 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1730 = true := by
  have hs : count1729 q = (countLit q [-72, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1727)) (literal (valuationOf q) (1730)) (countLit q [-72, -75]) (countLit q [-77, -79]) (count1729 q) 1 1 (meaning1725 q) (meaning1727 q) (meaning1730 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1727 = false ∨ valuation q 1730 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1731 = true := by
  have hs : count1729 q = (countLit q [-72, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1728)) (literal (valuationOf q) (1731)) (countLit q [-72, -75]) (countLit q [-77, -79]) (count1729 q) 1 2 (meaning1725 q) (meaning1728 q) (meaning1731 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1728 = false ∨ valuation q 1731 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1730 = true := by
  have hs : count1729 q = (countLit q [-72, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -79])
  have hm := merge_left (literal (valuationOf q) (1726)) (literal (valuationOf q) (1730)) (countLit q [-72, -75]) (countLit q [-77, -79]) (count1729 q) 2 (meaning1726 q) (meaning1730 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1730 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1731 = true := by
  have hs : count1729 q = (countLit q [-72, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1727)) (literal (valuationOf q) (1731)) (countLit q [-72, -75]) (countLit q [-77, -79]) (count1729 q) 2 1 (meaning1726 q) (meaning1727 q) (meaning1731 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1727 = false ∨ valuation q 1731 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1732 = true := by
  have hs : count1729 q = (countLit q [-72, -75]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1728)) (literal (valuationOf q) (1732)) (countLit q [-72, -75]) (countLit q [-77, -79]) (count1729 q) 2 2 (meaning1726 q) (meaning1728 q) (meaning1732 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1728 = false ∨ valuation q 1732 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_right (literal (valuationOf q) (1729)) (literal (valuationOf q) (1733)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 1 (meaning1729 q) (meaning1733 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1733 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_right (literal (valuationOf q) (1730)) (literal (valuationOf q) (1734)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 2 (meaning1730 q) (meaning1734 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1734 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1735 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_right (literal (valuationOf q) (1731)) (literal (valuationOf q) (1735)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 3 (meaning1731 q) (meaning1735 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1735 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1736 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_right (literal (valuationOf q) (1732)) (literal (valuationOf q) (1736)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 4 (meaning1732 q) (meaning1736 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1736 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_left (literal (valuationOf q) (1721)) (literal (valuationOf q) (1733)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 1 (meaning1721 q) (meaning1733 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1733 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1721)) (literal (valuationOf q) (1729)) (literal (valuationOf q) (1734)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 1 1 (meaning1721 q) (meaning1729 q) (meaning1734 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1729 = false ∨ valuation q 1734 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1735 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1721)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1735)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 1 2 (meaning1721 q) (meaning1730 q) (meaning1735 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1730 = false ∨ valuation q 1735 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1736 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1721)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1736)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 1 3 (meaning1721 q) (meaning1731 q) (meaning1736 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1731 = false ∨ valuation q 1736 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1737 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1721)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1737)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 1 4 (meaning1721 q) (meaning1732 q) (meaning1737 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1732 = false ∨ valuation q 1737 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_left (literal (valuationOf q) (1722)) (literal (valuationOf q) (1734)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 2 (meaning1722 q) (meaning1734 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1734 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1735 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1722)) (literal (valuationOf q) (1729)) (literal (valuationOf q) (1735)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 2 1 (meaning1722 q) (meaning1729 q) (meaning1735 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1729 = false ∨ valuation q 1735 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1736 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1722)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1736)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 2 2 (meaning1722 q) (meaning1730 q) (meaning1736 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1730 = false ∨ valuation q 1736 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1737 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1722)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1737)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 2 3 (meaning1722 q) (meaning1731 q) (meaning1737 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1731 = false ∨ valuation q 1737 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1738 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1722)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1738)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 2 4 (meaning1722 q) (meaning1732 q) (meaning1738 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1732 = false ∨ valuation q 1738 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1735 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_left (literal (valuationOf q) (1723)) (literal (valuationOf q) (1735)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 3 (meaning1723 q) (meaning1735 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1735 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1736 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1729)) (literal (valuationOf q) (1736)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 3 1 (meaning1723 q) (meaning1729 q) (meaning1736 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1729 = false ∨ valuation q 1736 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1737 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1737)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 3 2 (meaning1723 q) (meaning1730 q) (meaning1737 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1730 = false ∨ valuation q 1737 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1738 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1738)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 3 3 (meaning1723 q) (meaning1731 q) (meaning1738 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1731 = false ∨ valuation q 1738 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1739 = true := by
  have hs : count1733 q = (countLit q [-64, -67, -69, -71]) + (countLit q [-72, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71]) (l₂ := [-72, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1739)) (countLit q [-64, -67, -69, -71]) (countLit q [-72, -75, -77, -79]) (count1733 q) 3 4 (meaning1723 q) (meaning1732 q) (meaning1739 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1732 = false ∨ valuation q 1739 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1741)) (countLit q [-81]) (countLit q [-82]) (count1741 q) 1 (meaningNeg82 q) (meaning1741 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1741 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1741)) (countLit q [-81]) (countLit q [-82]) (count1741 q) 1 (meaningNeg81 q) (meaning1741 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1741 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1742 = true := by
  have hs : count1741 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1742)) (countLit q [-81]) (countLit q [-82]) (count1741 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning1742 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1742 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 1742 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1743)) (countLit q [-85]) (countLit q [-86]) (count1743 q) 1 (meaningNeg86 q) (meaning1743 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1743 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1743)) (countLit q [-85]) (countLit q [-86]) (count1743 q) 1 (meaningNeg85 q) (meaning1743 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1743 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1744)) (countLit q [-85]) (countLit q [-86]) (count1743 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning1744 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 1744 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1745 = true := by
  have hs : count1745 q = (countLit q [-81, -82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1743)) (literal (valuationOf q) (1745)) (countLit q [-81, -82]) (countLit q [-85, -86]) (count1745 q) 1 (meaning1743 q) (meaning1745 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1745 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E055.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112055
