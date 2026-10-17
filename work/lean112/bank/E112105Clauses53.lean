import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1739 = true := by
  have hs : count1739 q = (countLit q [-108, -110]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-108, -110]) (l₂ := [-113, -115])
  have hm := merge_right (literal (valuationOf q) (1737)) (literal (valuationOf q) (1739)) (countLit q [-108, -110]) (countLit q [-113, -115]) (count1739 q) 1 (meaning1737 q) (meaning1739 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1739 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1740 = true := by
  have hs : count1739 q = (countLit q [-108, -110]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-108, -110]) (l₂ := [-113, -115])
  have hm := merge_right (literal (valuationOf q) (1738)) (literal (valuationOf q) (1740)) (countLit q [-108, -110]) (countLit q [-113, -115]) (count1739 q) 2 (meaning1738 q) (meaning1740 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1740 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1740 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1739 = true := by
  have hs : count1739 q = (countLit q [-108, -110]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-108, -110]) (l₂ := [-113, -115])
  have hm := merge_left (literal (valuationOf q) (1735)) (literal (valuationOf q) (1739)) (countLit q [-108, -110]) (countLit q [-113, -115]) (count1739 q) 1 (meaning1735 q) (meaning1739 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1739 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1740 = true := by
  have hs : count1739 q = (countLit q [-108, -110]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-108, -110]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1740)) (countLit q [-108, -110]) (countLit q [-113, -115]) (count1739 q) 1 1 (meaning1735 q) (meaning1737 q) (meaning1740 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1740 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1737 = false ∨ valuation q 1740 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1741 = true := by
  have hs : count1739 q = (countLit q [-108, -110]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-108, -110]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1741)) (countLit q [-108, -110]) (countLit q [-113, -115]) (count1739 q) 1 2 (meaning1735 q) (meaning1738 q) (meaning1741 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1738 = false ∨ valuation q 1741 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1740 = true := by
  have hs : count1739 q = (countLit q [-108, -110]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-108, -110]) (l₂ := [-113, -115])
  have hm := merge_left (literal (valuationOf q) (1736)) (literal (valuationOf q) (1740)) (countLit q [-108, -110]) (countLit q [-113, -115]) (count1739 q) 2 (meaning1736 q) (meaning1740 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1740 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1740 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1741 = true := by
  have hs : count1739 q = (countLit q [-108, -110]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-108, -110]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1741)) (countLit q [-108, -110]) (countLit q [-113, -115]) (count1739 q) 2 1 (meaning1736 q) (meaning1737 q) (meaning1741 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1737 = false ∨ valuation q 1741 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1742 = true := by
  have hs : count1739 q = (countLit q [-108, -110]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-108, -110]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1742)) (countLit q [-108, -110]) (countLit q [-113, -115]) (count1739 q) 2 2 (meaning1736 q) (meaning1738 q) (meaning1742 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1738 = false ∨ valuation q 1742 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1743)) (countLit q [-116]) (countLit q [-117]) (count1743 q) 1 (meaningNeg117 q) (meaning1743 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1743 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-116)) (literal (valuationOf q) (1743)) (countLit q [-116]) (countLit q [-117]) (count1743 q) 1 (meaningNeg116 q) (meaning1743 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1743 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-116]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-116)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1744)) (countLit q [-116]) (countLit q [-117]) (count1743 q) 1 1 (meaningNeg116 q) (meaningNeg117 q) (meaning1744 q) hs
  change (! (valuationOf q 116)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 1744 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1745 = true := by
  have hs : count1745 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1745)) (countLit q [-122]) (countLit q [-123]) (count1745 q) 1 (meaningNeg123 q) (meaning1745 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1745 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1745 = true := by
  have hs : count1745 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_left (literal (valuationOf q) (-122)) (literal (valuationOf q) (1745)) (countLit q [-122]) (countLit q [-123]) (count1745 q) 1 (meaningNeg122 q) (meaning1745 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1745 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 123 = true ∨ valuationOf q 1746 = true := by
  have hs : count1745 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_two (literal (valuationOf q) (-122)) (literal (valuationOf q) (-123)) (literal (valuationOf q) (1746)) (countLit q [-122]) (countLit q [-123]) (count1745 q) 1 1 (meaningNeg122 q) (meaningNeg123 q) (meaning1746 q) hs
  change (! (valuationOf q 122)) = false ∨ (! (valuationOf q 123)) = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 1746 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1747 = true := by
  have hs : count1747 q = (countLit q [-116, -117]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-116, -117]) (l₂ := [-122, -123])
  have hm := merge_right (literal (valuationOf q) (1745)) (literal (valuationOf q) (1747)) (countLit q [-116, -117]) (countLit q [-122, -123]) (count1747 q) 1 (meaning1745 q) (meaning1747 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1747 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-116, -117]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-116, -117]) (l₂ := [-122, -123])
  have hm := merge_right (literal (valuationOf q) (1746)) (literal (valuationOf q) (1748)) (countLit q [-116, -117]) (countLit q [-122, -123]) (count1747 q) 2 (meaning1746 q) (meaning1748 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1748 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1747 = true := by
  have hs : count1747 q = (countLit q [-116, -117]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-116, -117]) (l₂ := [-122, -123])
  have hm := merge_left (literal (valuationOf q) (1743)) (literal (valuationOf q) (1747)) (countLit q [-116, -117]) (countLit q [-122, -123]) (count1747 q) 1 (meaning1743 q) (meaning1747 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1747 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-116, -117]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-116, -117]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1743)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1748)) (countLit q [-116, -117]) (countLit q [-122, -123]) (count1747 q) 1 1 (meaning1743 q) (meaning1745 q) (meaning1748 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1745 = false ∨ valuation q 1748 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-116, -117]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-116, -117]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1743)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1749)) (countLit q [-116, -117]) (countLit q [-122, -123]) (count1747 q) 1 2 (meaning1743 q) (meaning1746 q) (meaning1749 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1746 = false ∨ valuation q 1749 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-116, -117]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-116, -117]) (l₂ := [-122, -123])
  have hm := merge_left (literal (valuationOf q) (1744)) (literal (valuationOf q) (1748)) (countLit q [-116, -117]) (countLit q [-122, -123]) (count1747 q) 2 (meaning1744 q) (meaning1748 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1748 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-116, -117]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-116, -117]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1744)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1749)) (countLit q [-116, -117]) (countLit q [-122, -123]) (count1747 q) 2 1 (meaning1744 q) (meaning1745 q) (meaning1749 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1745 = false ∨ valuation q 1749 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-116, -117]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-116, -117]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1744)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1750)) (countLit q [-116, -117]) (countLit q [-122, -123]) (count1747 q) 2 2 (meaning1744 q) (meaning1746 q) (meaning1750 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1746 = false ∨ valuation q 1750 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1751 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1747)) (literal (valuationOf q) (1751)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 1 (meaning1747 q) (meaning1751 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1751 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1752 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1748)) (literal (valuationOf q) (1752)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 2 (meaning1748 q) (meaning1752 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1752 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1753 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1749)) (literal (valuationOf q) (1753)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 3 (meaning1749 q) (meaning1753 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1753 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1754 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1750)) (literal (valuationOf q) (1754)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 4 (meaning1750 q) (meaning1754 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1754 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1751 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1739)) (literal (valuationOf q) (1751)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 1 (meaning1739 q) (meaning1751 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1751 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1752 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1752)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 1 1 (meaning1739 q) (meaning1747 q) (meaning1752 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1747 = false ∨ valuation q 1752 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1753 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1753)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 1 2 (meaning1739 q) (meaning1748 q) (meaning1753 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1748 = false ∨ valuation q 1753 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1754 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1754)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 1 3 (meaning1739 q) (meaning1749 q) (meaning1754 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1749 = false ∨ valuation q 1754 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1755 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1755)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 1 4 (meaning1739 q) (meaning1750 q) (meaning1755 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1750 = false ∨ valuation q 1755 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1752 = true := by
  have hs : count1751 q = (countLit q [-108, -110, -113, -115]) + (countLit q [-116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-108, -110, -113, -115]) (l₂ := [-116, -117, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1740)) (literal (valuationOf q) (1752)) (countLit q [-108, -110, -113, -115]) (countLit q [-116, -117, -122, -123]) (count1751 q) 2 (meaning1740 q) (meaning1752 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1752 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E105.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112105
