import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1680 = true := by
  have hs : count1680 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1680)) (countLit q [-89]) (countLit q [-91]) (count1680 q) 1 (meaningNeg89 q) (meaning1680 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1680 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1681 = true := by
  have hs : count1680 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1681)) (countLit q [-89]) (countLit q [-91]) (count1680 q) 1 1 (meaningNeg89 q) (meaningNeg91 q) (meaning1681 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 1681 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1682 = true := by
  have hs : count1682 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_right (literal (valuationOf q) (1680)) (literal (valuationOf q) (1682)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1682 q) 1 (meaning1680 q) (meaning1682 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1682 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1683 = true := by
  have hs : count1682 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_right (literal (valuationOf q) (1681)) (literal (valuationOf q) (1683)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1682 q) 2 (meaning1681 q) (meaning1683 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1683 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1682 = true := by
  have hs : count1682 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_left (literal (valuationOf q) (1678)) (literal (valuationOf q) (1682)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1682 q) 1 (meaning1678 q) (meaning1682 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1682 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1683 = true := by
  have hs : count1682 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1683)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1682 q) 1 1 (meaning1678 q) (meaning1680 q) (meaning1683 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1680 = false ∨ valuation q 1683 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1684 = true := by
  have hs : count1682 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1684)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1682 q) 1 2 (meaning1678 q) (meaning1681 q) (meaning1684 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1681 = false ∨ valuation q 1684 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1683 = true := by
  have hs : count1682 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_left (literal (valuationOf q) (1679)) (literal (valuationOf q) (1683)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1682 q) 2 (meaning1679 q) (meaning1683 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1683 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1684 = true := by
  have hs : count1682 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1684)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1682 q) 2 1 (meaning1679 q) (meaning1680 q) (meaning1684 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1680 = false ∨ valuation q 1684 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1685 = true := by
  have hs : count1682 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1685)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1682 q) 2 2 (meaning1679 q) (meaning1681 q) (meaning1685 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1681 = false ∨ valuation q 1685 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1686 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1682)) (literal (valuationOf q) (1686)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 1 (meaning1682 q) (meaning1686 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1686 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1683)) (literal (valuationOf q) (1687)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 2 (meaning1683 q) (meaning1687 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1687 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1688 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1684)) (literal (valuationOf q) (1688)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 3 (meaning1684 q) (meaning1688 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1688 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1689 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1685)) (literal (valuationOf q) (1689)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 4 (meaning1685 q) (meaning1689 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1689 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1686 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1674)) (literal (valuationOf q) (1686)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 1 (meaning1674 q) (meaning1686 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1686 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1687)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 1 1 (meaning1674 q) (meaning1682 q) (meaning1687 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1682 = false ∨ valuation q 1687 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1688 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1688)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 1 2 (meaning1674 q) (meaning1683 q) (meaning1688 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1683 = false ∨ valuation q 1688 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1689 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1689)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 1 3 (meaning1674 q) (meaning1684 q) (meaning1689 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1684 = false ∨ valuation q 1689 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1690 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1690)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 1 4 (meaning1674 q) (meaning1685 q) (meaning1690 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1685 = false ∨ valuation q 1690 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1675)) (literal (valuationOf q) (1687)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 2 (meaning1675 q) (meaning1687 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1687 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1688)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 2 1 (meaning1675 q) (meaning1682 q) (meaning1688 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1682 = false ∨ valuation q 1688 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1689 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1689)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 2 2 (meaning1675 q) (meaning1683 q) (meaning1689 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1683 = false ∨ valuation q 1689 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1690 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1690)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 2 3 (meaning1675 q) (meaning1684 q) (meaning1690 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1684 = false ∨ valuation q 1690 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1691 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1691)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 2 4 (meaning1675 q) (meaning1685 q) (meaning1691 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1685 = false ∨ valuation q 1691 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1688 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1676)) (literal (valuationOf q) (1688)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 3 (meaning1676 q) (meaning1688 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1688 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1689 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1689)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 3 1 (meaning1676 q) (meaning1682 q) (meaning1689 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1682 = false ∨ valuation q 1689 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1690 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1690)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 3 2 (meaning1676 q) (meaning1683 q) (meaning1690 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1683 = false ∨ valuation q 1690 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1691 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1691)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 3 3 (meaning1676 q) (meaning1684 q) (meaning1691 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1684 = false ∨ valuation q 1691 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1692 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1692)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 3 4 (meaning1676 q) (meaning1685 q) (meaning1692 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1685 = false ∨ valuation q 1692 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1689 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1677)) (literal (valuationOf q) (1689)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 4 (meaning1677 q) (meaning1689 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1689 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1690 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1690)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 4 1 (meaning1677 q) (meaning1682 q) (meaning1690 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1682 = false ∨ valuation q 1690 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1692 = true := by
  have hs : count1686 q = (countLit q [-75, -76, -79, -81]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -79, -81]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1692)) (countLit q [-75, -76, -79, -81]) (countLit q [-85, -87, -89, -91]) (count1686 q) 4 3 (meaning1677 q) (meaning1684 q) (meaning1692 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1684 = false ∨ valuation q 1692 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E089.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112089
