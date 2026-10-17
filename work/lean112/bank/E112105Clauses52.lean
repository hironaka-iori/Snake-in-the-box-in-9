import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-102, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -105]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1719)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1725)) (countLit q [-102, -105]) (countLit q [-106, -107]) (count1723 q) 1 2 (meaning1719 q) (meaning1722 q) (meaning1725 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1722 = false ∨ valuation q 1725 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-102, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -105]) (l₂ := [-106, -107])
  have hm := merge_left (literal (valuationOf q) (1720)) (literal (valuationOf q) (1724)) (countLit q [-102, -105]) (countLit q [-106, -107]) (count1723 q) 2 (meaning1720 q) (meaning1724 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1724 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-102, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -105]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1720)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1725)) (countLit q [-102, -105]) (countLit q [-106, -107]) (count1723 q) 2 1 (meaning1720 q) (meaning1721 q) (meaning1725 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1721 = false ∨ valuation q 1725 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-102, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -105]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1720)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1726)) (countLit q [-102, -105]) (countLit q [-106, -107]) (count1723 q) 2 2 (meaning1720 q) (meaning1722 q) (meaning1726 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1722 = false ∨ valuation q 1726 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1727 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1723)) (literal (valuationOf q) (1727)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 1 (meaning1723 q) (meaning1727 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1727 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1728 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1724)) (literal (valuationOf q) (1728)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 2 (meaning1724 q) (meaning1728 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1728 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1729 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1725)) (literal (valuationOf q) (1729)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 3 (meaning1725 q) (meaning1729 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1729 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1730 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1726)) (literal (valuationOf q) (1730)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 4 (meaning1726 q) (meaning1730 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1730 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1727 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1727)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 1 (meaning1715 q) (meaning1727 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1727 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1728 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1728)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 1 1 (meaning1715 q) (meaning1723 q) (meaning1728 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1723 = false ∨ valuation q 1728 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1729 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1729)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 1 2 (meaning1715 q) (meaning1724 q) (meaning1729 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1724 = false ∨ valuation q 1729 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1730 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1730)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 1 3 (meaning1715 q) (meaning1725 q) (meaning1730 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1725 = false ∨ valuation q 1730 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1731 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1731)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 1 4 (meaning1715 q) (meaning1726 q) (meaning1731 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1726 = false ∨ valuation q 1731 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1728 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_left (literal (valuationOf q) (1716)) (literal (valuationOf q) (1728)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 2 (meaning1716 q) (meaning1728 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1728 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1729 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1729)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 2 1 (meaning1716 q) (meaning1723 q) (meaning1729 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1723 = false ∨ valuation q 1729 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1730 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1730)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 2 2 (meaning1716 q) (meaning1724 q) (meaning1730 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1724 = false ∨ valuation q 1730 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1731 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1731)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 2 3 (meaning1716 q) (meaning1725 q) (meaning1731 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1725 = false ∨ valuation q 1731 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1732 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1732)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 2 4 (meaning1716 q) (meaning1726 q) (meaning1732 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1726 = false ∨ valuation q 1732 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1729 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_left (literal (valuationOf q) (1717)) (literal (valuationOf q) (1729)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 3 (meaning1717 q) (meaning1729 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1729 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1730 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1730)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 3 1 (meaning1717 q) (meaning1723 q) (meaning1730 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1723 = false ∨ valuation q 1730 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1731 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1731)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 3 2 (meaning1717 q) (meaning1724 q) (meaning1731 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1724 = false ∨ valuation q 1731 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1732 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1732)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 3 3 (meaning1717 q) (meaning1725 q) (meaning1732 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1725 = false ∨ valuation q 1732 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1733 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1733)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 3 4 (meaning1717 q) (meaning1726 q) (meaning1733 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1726 = false ∨ valuation q 1733 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1731 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1718)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1731)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 4 1 (meaning1718 q) (meaning1723 q) (meaning1731 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1723 = false ∨ valuation q 1731 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1732 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1718)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1732)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 4 2 (meaning1718 q) (meaning1724 q) (meaning1732 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1724 = false ∨ valuation q 1732 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1734 = true := by
  have hs : count1727 q = (countLit q [-95, -98, -99, -101]) + (countLit q [-102, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101]) (l₂ := [-102, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1718)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1734)) (countLit q [-95, -98, -99, -101]) (countLit q [-102, -105, -106, -107]) (count1727 q) 4 4 (meaning1718 q) (meaning1726 q) (meaning1734 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1726 = false ∨ valuation q 1734 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1735)) (countLit q [-108]) (countLit q [-110]) (count1735 q) 1 (meaningNeg110 q) (meaning1735 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1735 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-108)) (literal (valuationOf q) (1735)) (countLit q [-108]) (countLit q [-110]) (count1735 q) 1 (meaningNeg108 q) (meaning1735 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1735 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-108)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1736)) (countLit q [-108]) (countLit q [-110]) (count1735 q) 1 1 (meaningNeg108 q) (meaningNeg110 q) (meaning1736 q) hs
  change (! (valuationOf q 108)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 1736 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_right (literal (valuationOf q) (-115)) (literal (valuationOf q) (1737)) (countLit q [-113]) (countLit q [-115]) (count1737 q) 1 (meaningNeg115 q) (meaning1737 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1737 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1737)) (countLit q [-113]) (countLit q [-115]) (count1737 q) 1 (meaningNeg113 q) (meaning1737 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1737 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 115 = true ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-115)) (literal (valuationOf q) (1738)) (countLit q [-113]) (countLit q [-115]) (count1737 q) 1 1 (meaningNeg113 q) (meaningNeg115 q) (meaning1738 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 115)) = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 115 = true ∨ valuation q 1738 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E105.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112105
