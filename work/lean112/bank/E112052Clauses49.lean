import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_left (literal (valuationOf q) (1700)) (literal (valuationOf q) (1712)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 2 (meaning1700 q) (meaning1712 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1712 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1713)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 2 1 (meaning1700 q) (meaning1707 q) (meaning1713 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1707 = false ∨ valuation q 1713 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1714 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1714)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 2 2 (meaning1700 q) (meaning1708 q) (meaning1714 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1708 = false ∨ valuation q 1714 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1715 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1715)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 2 3 (meaning1700 q) (meaning1709 q) (meaning1715 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1709 = false ∨ valuation q 1715 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_left (literal (valuationOf q) (1701)) (literal (valuationOf q) (1713)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 3 (meaning1701 q) (meaning1713 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1713 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1714 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1714)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 3 1 (meaning1701 q) (meaning1707 q) (meaning1714 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1707 = false ∨ valuation q 1714 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1715 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1715)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 3 2 (meaning1701 q) (meaning1708 q) (meaning1715 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1708 = false ∨ valuation q 1715 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1716 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1716)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 3 3 (meaning1701 q) (meaning1709 q) (meaning1716 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1709 = false ∨ valuation q 1716 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1717 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1717)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 3 4 (meaning1701 q) (meaning1710 q) (meaning1717 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1710 = false ∨ valuation q 1717 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1714 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_left (literal (valuationOf q) (1702)) (literal (valuationOf q) (1714)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 4 (meaning1702 q) (meaning1714 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1714 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1715 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1715)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 4 1 (meaning1702 q) (meaning1707 q) (meaning1715 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1707 = false ∨ valuation q 1715 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1716 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1716)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 4 2 (meaning1702 q) (meaning1708 q) (meaning1716 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1708 = false ∨ valuation q 1716 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1717 = true := by
  have hs : count1711 q = (countLit q [-65, -67, -68, -71]) + (countLit q [-72, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71]) (l₂ := [-72, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1717)) (countLit q [-65, -67, -68, -71]) (countLit q [-72, -77, -78, -81]) (count1711 q) 4 3 (meaning1702 q) (meaning1709 q) (meaning1717 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1709 = false ∨ valuation q 1717 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1719)) (countLit q [-82]) (countLit q [-84]) (count1719 q) 1 (meaningNeg84 q) (meaning1719 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1719 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1719)) (countLit q [-82]) (countLit q [-84]) (count1719 q) 1 (meaningNeg82 q) (meaning1719 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1719 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1720)) (countLit q [-82]) (countLit q [-84]) (count1719 q) 1 1 (meaningNeg82 q) (meaningNeg84 q) (meaning1720 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 1720 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1721)) (countLit q [-86]) (countLit q [-87]) (count1721 q) 1 (meaningNeg87 q) (meaning1721 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1721 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1721)) (countLit q [-86]) (countLit q [-87]) (count1721 q) 1 (meaningNeg86 q) (meaning1721 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1721 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1722)) (countLit q [-86]) (countLit q [-87]) (count1721 q) 1 1 (meaningNeg86 q) (meaningNeg87 q) (meaning1722 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 1722 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1721)) (literal (valuationOf q) (1723)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1723 q) 1 (meaning1721 q) (meaning1723 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1723 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1722)) (literal (valuationOf q) (1724)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1723 q) 2 (meaning1722 q) (meaning1724 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1724 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_left (literal (valuationOf q) (1719)) (literal (valuationOf q) (1723)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1723 q) 1 (meaning1719 q) (meaning1723 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1723 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1719)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1724)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1723 q) 1 1 (meaning1719 q) (meaning1721 q) (meaning1724 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1721 = false ∨ valuation q 1724 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1719)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1725)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1723 q) 1 2 (meaning1719 q) (meaning1722 q) (meaning1725 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1722 = false ∨ valuation q 1725 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_left (literal (valuationOf q) (1720)) (literal (valuationOf q) (1724)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1723 q) 2 (meaning1720 q) (meaning1724 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1724 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1720)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1725)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1723 q) 2 1 (meaning1720 q) (meaning1721 q) (meaning1725 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1721 = false ∨ valuation q 1725 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1720)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1726)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1723 q) 2 2 (meaning1720 q) (meaning1722 q) (meaning1726 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1722 = false ∨ valuation q 1726 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1727 = true := by
  have hs : count1727 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1727)) (countLit q [-90]) (countLit q [-91]) (count1727 q) 1 (meaningNeg91 q) (meaning1727 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1727 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1727 = true := by
  have hs : count1727 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1727)) (countLit q [-90]) (countLit q [-91]) (count1727 q) 1 (meaningNeg90 q) (meaning1727 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1727 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1728 = true := by
  have hs : count1727 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1728)) (countLit q [-90]) (countLit q [-91]) (count1727 q) 1 1 (meaningNeg90 q) (meaningNeg91 q) (meaning1728 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 91 = true ∨ valuation q 1728 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1729 = true := by
  have hs : count1729 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1729)) (countLit q [-94]) (countLit q [-95]) (count1729 q) 1 (meaningNeg95 q) (meaning1729 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1729 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1729 = true := by
  have hs : count1729 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1729)) (countLit q [-94]) (countLit q [-95]) (count1729 q) 1 (meaningNeg94 q) (meaning1729 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1729 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E052.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112052
