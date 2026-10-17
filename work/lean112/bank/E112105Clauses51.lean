import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1700)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 4 1 (meaning1668 q) (meaning1688 q) (meaning1700 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1688 = false ∨ valuation q 1700 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1701 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1701)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 4 2 (meaning1668 q) (meaning1689 q) (meaning1701 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1689 = false ∨ valuation q 1701 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1702 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1702)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 4 3 (meaning1668 q) (meaning1690 q) (meaning1702 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1690 = false ∨ valuation q 1702 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1703 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1703)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 4 4 (meaning1668 q) (meaning1691 q) (meaning1703 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1691 = false ∨ valuation q 1703 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1700 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1669)) (literal (valuationOf q) (1700)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 5 (meaning1669 q) (meaning1700 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1700 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1701 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1701)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 5 1 (meaning1669 q) (meaning1688 q) (meaning1701 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1688 = false ∨ valuation q 1701 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1702 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1702)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 5 2 (meaning1669 q) (meaning1689 q) (meaning1702 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1689 = false ∨ valuation q 1702 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1703 = true := by
  have hs : count1696 q = (countLit q [-64, -66, -68, -71, -72, -74, -76]) + (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76]) (l₂ := [-78, -81, -83, -85, -88, -89, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1703)) (countLit q [-64, -66, -68, -71, -72, -74, -76]) (countLit q [-78, -81, -83, -85, -88, -89, -91, -93]) (count1696 q) 5 3 (meaning1669 q) (meaning1690 q) (meaning1703 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1690 = false ∨ valuation q 1703 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1711)) (countLit q [-95]) (countLit q [-98]) (count1711 q) 1 (meaningNeg98 q) (meaning1711 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1711 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1711)) (countLit q [-95]) (countLit q [-98]) (count1711 q) 1 (meaningNeg95 q) (meaning1711 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1711 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1712)) (countLit q [-95]) (countLit q [-98]) (count1711 q) 1 1 (meaningNeg95 q) (meaningNeg98 q) (meaning1712 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 98 = true ∨ valuation q 1712 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1713 = true := by
  have hs : count1713 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1713)) (countLit q [-99]) (countLit q [-101]) (count1713 q) 1 (meaningNeg101 q) (meaning1713 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1713 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1713 = true := by
  have hs : count1713 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1713)) (countLit q [-99]) (countLit q [-101]) (count1713 q) 1 (meaningNeg99 q) (meaning1713 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1713 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1714 = true := by
  have hs : count1713 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1714)) (countLit q [-99]) (countLit q [-101]) (count1713 q) 1 1 (meaningNeg99 q) (meaningNeg101 q) (meaning1714 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 101 = true ∨ valuation q 1714 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1713)) (literal (valuationOf q) (1715)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1715 q) 1 (meaning1713 q) (meaning1715 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1715 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1716 = true := by
  have hs : count1715 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1714)) (literal (valuationOf q) (1716)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1715 q) 2 (meaning1714 q) (meaning1716 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1716 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (1711)) (literal (valuationOf q) (1715)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1715 q) 1 (meaning1711 q) (meaning1715 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1715 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1716 = true := by
  have hs : count1715 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1716)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1715 q) 1 1 (meaning1711 q) (meaning1713 q) (meaning1716 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1713 = false ∨ valuation q 1716 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1717 = true := by
  have hs : count1715 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1717)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1715 q) 1 2 (meaning1711 q) (meaning1714 q) (meaning1717 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1714 = false ∨ valuation q 1717 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1716 = true := by
  have hs : count1715 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (1712)) (literal (valuationOf q) (1716)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1715 q) 2 (meaning1712 q) (meaning1716 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1716 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1717 = true := by
  have hs : count1715 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1717)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1715 q) 2 1 (meaning1712 q) (meaning1713 q) (meaning1717 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1713 = false ∨ valuation q 1717 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1718 = true := by
  have hs : count1715 q = (countLit q [-95, -98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1718)) (countLit q [-95, -98]) (countLit q [-99, -101]) (count1715 q) 2 2 (meaning1712 q) (meaning1714 q) (meaning1718 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1714 = false ∨ valuation q 1718 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1719)) (countLit q [-102]) (countLit q [-105]) (count1719 q) 1 (meaningNeg105 q) (meaning1719 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1719 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1719)) (countLit q [-102]) (countLit q [-105]) (count1719 q) 1 (meaningNeg102 q) (meaning1719 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1719 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1720)) (countLit q [-102]) (countLit q [-105]) (count1719 q) 1 1 (meaningNeg102 q) (meaningNeg105 q) (meaning1720 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 1720 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1721)) (countLit q [-106]) (countLit q [-107]) (count1721 q) 1 (meaningNeg107 q) (meaning1721 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1721 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1721)) (countLit q [-106]) (countLit q [-107]) (count1721 q) 1 (meaningNeg106 q) (meaning1721 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1721 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1722)) (countLit q [-106]) (countLit q [-107]) (count1721 q) 1 1 (meaningNeg106 q) (meaningNeg107 q) (meaning1722 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 1722 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-102, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -105]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1721)) (literal (valuationOf q) (1723)) (countLit q [-102, -105]) (countLit q [-106, -107]) (count1723 q) 1 (meaning1721 q) (meaning1723 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1723 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-102, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -105]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1722)) (literal (valuationOf q) (1724)) (countLit q [-102, -105]) (countLit q [-106, -107]) (count1723 q) 2 (meaning1722 q) (meaning1724 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1724 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-102, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -105]) (l₂ := [-106, -107])
  have hm := merge_left (literal (valuationOf q) (1719)) (literal (valuationOf q) (1723)) (countLit q [-102, -105]) (countLit q [-106, -107]) (count1723 q) 1 (meaning1719 q) (meaning1723 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1723 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-102, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -105]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1719)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1724)) (countLit q [-102, -105]) (countLit q [-106, -107]) (count1723 q) 1 1 (meaning1719 q) (meaning1721 q) (meaning1724 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1721 = false ∨ valuation q 1724 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E105.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112105
