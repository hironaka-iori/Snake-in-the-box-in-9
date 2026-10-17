import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1698 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_right (literal (valuationOf q) (1690)) (literal (valuationOf q) (1698)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 7 (meaning1690 q) (meaning1698 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1698 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1695 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1695)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 1 3 (meaning1661 q) (meaning1686 q) (meaning1695 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1686 = false ∨ valuation q 1695 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1696 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1696)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 1 4 (meaning1661 q) (meaning1687 q) (meaning1696 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1687 = false ∨ valuation q 1696 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1697)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 1 5 (meaning1661 q) (meaning1688 q) (meaning1697 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1688 = false ∨ valuation q 1697 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1698)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 1 6 (meaning1661 q) (meaning1689 q) (meaning1698 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1689 = false ∨ valuation q 1698 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1699 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1699)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 1 7 (meaning1661 q) (meaning1690 q) (meaning1699 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1690 = false ∨ valuation q 1699 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1694 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1694)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 2 1 (meaning1662 q) (meaning1684 q) (meaning1694 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1684 = false ∨ valuation q 1694 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1695 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1695)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 2 2 (meaning1662 q) (meaning1685 q) (meaning1695 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1685 = false ∨ valuation q 1695 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1696)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 2 3 (meaning1662 q) (meaning1686 q) (meaning1696 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1686 = false ∨ valuation q 1696 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1697)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 2 4 (meaning1662 q) (meaning1687 q) (meaning1697 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1687 = false ∨ valuation q 1697 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1698)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 2 5 (meaning1662 q) (meaning1688 q) (meaning1698 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1688 = false ∨ valuation q 1698 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1699)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 2 6 (meaning1662 q) (meaning1689 q) (meaning1699 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1689 = false ∨ valuation q 1699 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1700 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1700)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 2 7 (meaning1662 q) (meaning1690 q) (meaning1700 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1690 = false ∨ valuation q 1700 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1695 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1695)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 3 1 (meaning1663 q) (meaning1684 q) (meaning1695 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1684 = false ∨ valuation q 1695 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1696 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1696)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 3 2 (meaning1663 q) (meaning1685 q) (meaning1696 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1685 = false ∨ valuation q 1696 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1697)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 3 3 (meaning1663 q) (meaning1686 q) (meaning1697 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1686 = false ∨ valuation q 1697 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1698 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1698)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 3 4 (meaning1663 q) (meaning1687 q) (meaning1698 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1687 = false ∨ valuation q 1698 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1699)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 3 5 (meaning1663 q) (meaning1688 q) (meaning1699 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1688 = false ∨ valuation q 1699 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1700 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1700)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 3 6 (meaning1663 q) (meaning1689 q) (meaning1700 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1689 = false ∨ valuation q 1700 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1701 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1701)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 3 7 (meaning1663 q) (meaning1690 q) (meaning1701 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1690 = false ∨ valuation q 1701 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1697 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1697)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 4 2 (meaning1664 q) (meaning1685 q) (meaning1697 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1685 = false ∨ valuation q 1697 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1698 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1698)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 4 3 (meaning1664 q) (meaning1686 q) (meaning1698 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1686 = false ∨ valuation q 1698 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1699 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1699)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 4 4 (meaning1664 q) (meaning1687 q) (meaning1699 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1687 = false ∨ valuation q 1699 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1700)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 4 5 (meaning1664 q) (meaning1688 q) (meaning1700 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1688 = false ∨ valuation q 1700 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1717 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1700)) (literal (valuationOf q) (1717)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 2 9 (meaning1634 q) (meaning1700 q) (meaning1717 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1700 = false ∨ valuation q 1717 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1716 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1716)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 3 7 (meaning1635 q) (meaning1698 q) (meaning1716 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1698 = false ∨ valuation q 1716 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1717 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1717)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 3 8 (meaning1635 q) (meaning1699 q) (meaning1717 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1699 = false ∨ valuation q 1717 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1718 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1700)) (literal (valuationOf q) (1718)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 3 9 (meaning1635 q) (meaning1700 q) (meaning1718 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1700 = false ∨ valuation q 1718 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1719 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1701)) (literal (valuationOf q) (1719)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 3 10 (meaning1635 q) (meaning1701 q) (meaning1719 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1701 = false ∨ valuation q 1719 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1715 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1715)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 4 5 (meaning1636 q) (meaning1696 q) (meaning1715 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1696 = false ∨ valuation q 1715 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1716 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1716)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 4 6 (meaning1636 q) (meaning1697 q) (meaning1716 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1697 = false ∨ valuation q 1716 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1717 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1717)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 4 7 (meaning1636 q) (meaning1698 q) (meaning1717 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1698 = false ∨ valuation q 1717 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E152.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112152
