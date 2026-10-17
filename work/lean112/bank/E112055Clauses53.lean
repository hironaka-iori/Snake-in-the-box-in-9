import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1782 = true := by
  have hs : count1781 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1782)) (countLit q [-99]) (countLit q [-100]) (count1781 q) 1 1 (meaningNeg99 q) (meaningNeg100 q) (meaning1782 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 1782 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1783 = true := by
  have hs : count1783 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1783)) (countLit q [-102]) (countLit q [-104]) (count1783 q) 1 (meaningNeg104 q) (meaning1783 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1783 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1783 = true := by
  have hs : count1783 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1783)) (countLit q [-102]) (countLit q [-104]) (count1783 q) 1 (meaningNeg102 q) (meaning1783 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1783 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1784 = true := by
  have hs : count1783 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1784)) (countLit q [-102]) (countLit q [-104]) (count1783 q) 1 1 (meaningNeg102 q) (meaningNeg104 q) (meaning1784 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 104 = true ∨ valuation q 1784 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1783 = false ∨ valuationOf q 1785 = true := by
  have hs : count1785 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_right (literal (valuationOf q) (1783)) (literal (valuationOf q) (1785)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1785 q) 1 (meaning1783 q) (meaning1785 q) hs
  change valuationOf q 1783 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1783 = false ∨ valuation q 1785 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1784 = false ∨ valuationOf q 1786 = true := by
  have hs : count1785 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_right (literal (valuationOf q) (1784)) (literal (valuationOf q) (1786)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1785 q) 2 (meaning1784 q) (meaning1786 q) hs
  change valuationOf q 1784 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1784 = false ∨ valuation q 1786 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1785 = true := by
  have hs : count1785 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_left (literal (valuationOf q) (1781)) (literal (valuationOf q) (1785)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1785 q) 1 (meaning1781 q) (meaning1785 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1785 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1786 = true := by
  have hs : count1785 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (1781)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1786)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1785 q) 1 1 (meaning1781 q) (meaning1783 q) (meaning1786 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1783 = false ∨ valuation q 1786 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1787 = true := by
  have hs : count1785 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (1781)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1787)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1785 q) 1 2 (meaning1781 q) (meaning1784 q) (meaning1787 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1784 = false ∨ valuation q 1787 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1782 = false ∨ valuationOf q 1786 = true := by
  have hs : count1785 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_left (literal (valuationOf q) (1782)) (literal (valuationOf q) (1786)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1785 q) 2 (meaning1782 q) (meaning1786 q) hs
  change valuationOf q 1782 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1782 = false ∨ valuation q 1786 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1782 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1787 = true := by
  have hs : count1785 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (1782)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1787)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1785 q) 2 1 (meaning1782 q) (meaning1783 q) (meaning1787 q) hs
  change valuationOf q 1782 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1782 = false ∨ valuation q 1783 = false ∨ valuation q 1787 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1782 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1788 = true := by
  have hs : count1785 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (1782)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1788)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1785 q) 2 2 (meaning1782 q) (meaning1784 q) (meaning1788 q) hs
  change valuationOf q 1782 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1782 = false ∨ valuation q 1784 = false ∨ valuation q 1788 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1789 = true := by
  have hs : count1789 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1789)) (countLit q [-106]) (countLit q [-108]) (count1789 q) 1 (meaningNeg108 q) (meaning1789 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1789 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1789 = true := by
  have hs : count1789 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1789)) (countLit q [-106]) (countLit q [-108]) (count1789 q) 1 (meaningNeg106 q) (meaning1789 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1789 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1790 = true := by
  have hs : count1789 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1790)) (countLit q [-106]) (countLit q [-108]) (count1789 q) 1 1 (meaningNeg106 q) (meaningNeg108 q) (meaning1790 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1790 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 1790 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1791 = true := by
  have hs : count1791 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1791)) (countLit q [-110]) (countLit q [-111]) (count1791 q) 1 (meaningNeg111 q) (meaning1791 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1791 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1791 = true := by
  have hs : count1791 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1791)) (countLit q [-110]) (countLit q [-111]) (count1791 q) 1 (meaningNeg110 q) (meaning1791 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1791 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 111 = true ∨ valuationOf q 1792 = true := by
  have hs : count1791 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_two (literal (valuationOf q) (-110)) (literal (valuationOf q) (-111)) (literal (valuationOf q) (1792)) (countLit q [-110]) (countLit q [-111]) (count1791 q) 1 1 (meaningNeg110 q) (meaningNeg111 q) (meaning1792 q) hs
  change (! (valuationOf q 110)) = false ∨ (! (valuationOf q 111)) = false ∨ valuationOf q 1792 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 1792 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1793 = true := by
  have hs : count1793 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1791)) (literal (valuationOf q) (1793)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1793 q) 1 (meaning1791 q) (meaning1793 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1793 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1794 = true := by
  have hs : count1793 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1792)) (literal (valuationOf q) (1794)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1793 q) 2 (meaning1792 q) (meaning1794 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1794 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1793 = true := by
  have hs : count1793 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_left (literal (valuationOf q) (1789)) (literal (valuationOf q) (1793)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1793 q) 1 (meaning1789 q) (meaning1793 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1793 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1791 = false ∨ valuationOf q 1794 = true := by
  have hs : count1793 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1791)) (literal (valuationOf q) (1794)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1793 q) 1 1 (meaning1789 q) (meaning1791 q) (meaning1794 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1791 = false ∨ valuationOf q 1794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1791 = false ∨ valuation q 1794 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1792 = false ∨ valuationOf q 1795 = true := by
  have hs : count1793 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1792)) (literal (valuationOf q) (1795)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1793 q) 1 2 (meaning1789 q) (meaning1792 q) (meaning1795 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1792 = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1792 = false ∨ valuation q 1795 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1794 = true := by
  have hs : count1793 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_left (literal (valuationOf q) (1790)) (literal (valuationOf q) (1794)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1793 q) 2 (meaning1790 q) (meaning1794 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1794 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1791 = false ∨ valuationOf q 1795 = true := by
  have hs : count1793 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1791)) (literal (valuationOf q) (1795)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1793 q) 2 1 (meaning1790 q) (meaning1791 q) (meaning1795 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1791 = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1791 = false ∨ valuation q 1795 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1792 = false ∨ valuationOf q 1796 = true := by
  have hs : count1793 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1792)) (literal (valuationOf q) (1796)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1793 q) 2 2 (meaning1790 q) (meaning1792 q) (meaning1796 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1792 = false ∨ valuationOf q 1796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1792 = false ∨ valuation q 1796 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_right (literal (valuationOf q) (1793)) (literal (valuationOf q) (1797)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 1 (meaning1793 q) (meaning1797 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1797 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 1794 = false ∨ valuationOf q 1798 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_right (literal (valuationOf q) (1794)) (literal (valuationOf q) (1798)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 2 (meaning1794 q) (meaning1798 q) hs
  change valuationOf q 1794 = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 1794 = false ∨ valuation q 1798 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1799 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_right (literal (valuationOf q) (1795)) (literal (valuationOf q) (1799)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 3 (meaning1795 q) (meaning1799 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1799 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 1796 = false ∨ valuationOf q 1800 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_right (literal (valuationOf q) (1796)) (literal (valuationOf q) (1800)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 4 (meaning1796 q) (meaning1800 q) hs
  change valuationOf q 1796 = false ∨ valuationOf q 1800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 1796 = false ∨ valuation q 1800 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_left (literal (valuationOf q) (1785)) (literal (valuationOf q) (1797)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 1 (meaning1785 q) (meaning1797 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1797 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 1785 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1798 = true := by
  have hs : count1797 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_two (literal (valuationOf q) (1785)) (literal (valuationOf q) (1793)) (literal (valuationOf q) (1798)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1797 q) 1 1 (meaning1785 q) (meaning1793 q) (meaning1798 q) hs
  change valuationOf q 1785 = false ∨ valuationOf q 1793 = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 1785 = false ∨ valuation q 1793 = false ∨ valuation q 1798 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E055.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112055
