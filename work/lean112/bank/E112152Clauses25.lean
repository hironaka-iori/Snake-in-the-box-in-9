import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1657 q = (countLit q [-96, -99]) + (countLit q [-100, -104]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -104])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-96, -99]) (countLit q [-100, -104]) (count1657 q) 2 1 (meaning1654 q) (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1655 = false ∨ valuation q 1659 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1660 = true := by
  have hs : count1657 q = (countLit q [-96, -99]) + (countLit q [-100, -104]) := List.countP_append (p := literal q) (l₁ := [-96, -99]) (l₂ := [-100, -104])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1660)) (countLit q [-96, -99]) (countLit q [-100, -104]) (count1657 q) 2 2 (meaning1654 q) (meaning1656 q) (meaning1660 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1656 = false ∨ valuation q 1660 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1661 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1661)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 1 (meaning1657 q) (meaning1661 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1661 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_right (literal (valuationOf q) (1658)) (literal (valuationOf q) (1662)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 2 (meaning1658 q) (meaning1662 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1662 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1663 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_right (literal (valuationOf q) (1659)) (literal (valuationOf q) (1663)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 3 (meaning1659 q) (meaning1663 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1663 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1664 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_right (literal (valuationOf q) (1660)) (literal (valuationOf q) (1664)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 4 (meaning1660 q) (meaning1664 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1664 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1661 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_left (literal (valuationOf q) (1650)) (literal (valuationOf q) (1661)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 1 (meaning1650 q) (meaning1661 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1661 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1662)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 1 1 (meaning1650 q) (meaning1657 q) (meaning1662 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1657 = false ∨ valuation q 1662 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1663 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1663)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 1 2 (meaning1650 q) (meaning1658 q) (meaning1663 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1658 = false ∨ valuation q 1663 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1664 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1664)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 1 3 (meaning1650 q) (meaning1659 q) (meaning1664 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1659 = false ∨ valuation q 1664 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_left (literal (valuationOf q) (1651)) (literal (valuationOf q) (1662)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 2 (meaning1651 q) (meaning1662 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1662 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1663 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1663)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 2 1 (meaning1651 q) (meaning1657 q) (meaning1663 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1657 = false ∨ valuation q 1663 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1664 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1664)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 2 2 (meaning1651 q) (meaning1658 q) (meaning1664 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1658 = false ∨ valuation q 1664 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1664 = true := by
  have hs : count1661 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -99, -100, -104]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -99, -100, -104])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1664)) (countLit q [-90, -91, -94]) (countLit q [-96, -99, -100, -104]) (count1661 q) 3 1 (meaning1652 q) (meaning1657 q) (meaning1664 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1657 = false ∨ valuation q 1664 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1668 = true := by
  have hs : count1668 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1668)) (countLit q [-107]) (countLit q [-108]) (count1668 q) 1 (meaningNeg108 q) (meaning1668 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1668 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1668 = true := by
  have hs : count1668 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1668)) (countLit q [-107]) (countLit q [-108]) (count1668 q) 1 (meaningNeg107 q) (meaning1668 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1668 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1669)) (countLit q [-107]) (countLit q [-108]) (count1668 q) 1 1 (meaningNeg107 q) (meaningNeg108 q) (meaning1669 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 1669 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1670)) (countLit q [-112]) (countLit q [-113]) (count1670 q) 1 (meaningNeg113 q) (meaning1670 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1670 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1670)) (countLit q [-112]) (countLit q [-113]) (count1670 q) 1 (meaningNeg112 q) (meaning1670 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1670 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1671 = true := by
  have hs : count1670 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1671)) (countLit q [-112]) (countLit q [-113]) (count1670 q) 1 1 (meaningNeg112 q) (meaningNeg113 q) (meaning1671 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 1671 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-107, -108]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-112, -113])
  have hm := merge_right (literal (valuationOf q) (1670)) (literal (valuationOf q) (1672)) (countLit q [-107, -108]) (countLit q [-112, -113]) (count1672 q) 1 (meaning1670 q) (meaning1672 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1672 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1673 = true := by
  have hs : count1672 q = (countLit q [-107, -108]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-112, -113])
  have hm := merge_right (literal (valuationOf q) (1671)) (literal (valuationOf q) (1673)) (countLit q [-107, -108]) (countLit q [-112, -113]) (count1672 q) 2 (meaning1671 q) (meaning1673 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1673 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-107, -108]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-112, -113])
  have hm := merge_left (literal (valuationOf q) (1668)) (literal (valuationOf q) (1672)) (countLit q [-107, -108]) (countLit q [-112, -113]) (count1672 q) 1 (meaning1668 q) (meaning1672 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1672 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1673 = true := by
  have hs : count1672 q = (countLit q [-107, -108]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-112, -113])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1673)) (countLit q [-107, -108]) (countLit q [-112, -113]) (count1672 q) 1 1 (meaning1668 q) (meaning1670 q) (meaning1673 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1670 = false ∨ valuation q 1673 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1674 = true := by
  have hs : count1672 q = (countLit q [-107, -108]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-112, -113])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1674)) (countLit q [-107, -108]) (countLit q [-112, -113]) (count1672 q) 1 2 (meaning1668 q) (meaning1671 q) (meaning1674 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1671 = false ∨ valuation q 1674 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1673 = true := by
  have hs : count1672 q = (countLit q [-107, -108]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-112, -113])
  have hm := merge_left (literal (valuationOf q) (1669)) (literal (valuationOf q) (1673)) (countLit q [-107, -108]) (countLit q [-112, -113]) (count1672 q) 2 (meaning1669 q) (meaning1673 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1673 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1674 = true := by
  have hs : count1672 q = (countLit q [-107, -108]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-112, -113])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1674)) (countLit q [-107, -108]) (countLit q [-112, -113]) (count1672 q) 2 1 (meaning1669 q) (meaning1670 q) (meaning1674 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1670 = false ∨ valuation q 1674 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1675 = true := by
  have hs : count1672 q = (countLit q [-107, -108]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-112, -113])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1675)) (countLit q [-107, -108]) (countLit q [-112, -113]) (count1672 q) 2 2 (meaning1669 q) (meaning1671 q) (meaning1675 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1671 = false ∨ valuation q 1675 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1676 = true := by
  have hs : count1676 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1676)) (countLit q [-114]) (countLit q [-116]) (count1676 q) 1 (meaningNeg116 q) (meaning1676 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1676 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1676 = true := by
  have hs : count1676 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1676)) (countLit q [-114]) (countLit q [-116]) (count1676 q) 1 (meaningNeg114 q) (meaning1676 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1676 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1677 = true := by
  have hs : count1676 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-114)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1677)) (countLit q [-114]) (countLit q [-116]) (count1676 q) 1 1 (meaningNeg114 q) (meaningNeg116 q) (meaning1677 q) hs
  change (! (valuationOf q 114)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 1677 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1678 = true := by
  have hs : count1678 q = (countLit q [-117]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1678)) (countLit q [-117]) (countLit q [-120]) (count1678 q) 1 (meaningNeg120 q) (meaning1678 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1678 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E152.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112152
