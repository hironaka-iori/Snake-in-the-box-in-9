import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1761 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-8, -9])
  have hm := merge_left (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-3, -4]) (countLit q [-8, -9]) (count1533 q) 1 (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1533 = true := counterClause1761 (baseVal q)

theorem counterClause1762 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-8, -9])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (countLit q [-3, -4]) (countLit q [-8, -9]) (count1533 q) 1 1 (meaning1529 q) (meaning1531 q) (meaning1534 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = false ∨ valuation q 1534 = true := counterClause1762 (baseVal q)

theorem counterClause1763 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-8, -9])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1535)) (countLit q [-3, -4]) (countLit q [-8, -9]) (count1533 q) 1 2 (meaning1529 q) (meaning1532 q) (meaning1535 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1532 = false ∨ valuation q 1535 = true := counterClause1763 (baseVal q)

theorem counterClause1764 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-8, -9])
  have hm := merge_left (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-3, -4]) (countLit q [-8, -9]) (count1533 q) 2 (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1534 = true := counterClause1764 (baseVal q)

theorem counterClause1765 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-8, -9])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-3, -4]) (countLit q [-8, -9]) (count1533 q) 2 1 (meaning1530 q) (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1531 = false ∨ valuation q 1535 = true := counterClause1765 (baseVal q)

theorem counterClause1766 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-8, -9])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-3, -4]) (countLit q [-8, -9]) (count1533 q) 2 2 (meaning1530 q) (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1532 = false ∨ valuation q 1536 = true := counterClause1766 (baseVal q)

theorem counterClause1767 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1537)) (countLit q [-11]) (countLit q [-13]) (count1537 q) 1 (meaningNeg13 q) (meaning1537 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1537 = true := counterClause1767 (baseVal q)

theorem counterClause1768 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1537)) (countLit q [-11]) (countLit q [-13]) (count1537 q) 1 (meaningNeg11 q) (meaning1537 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1537 = true := counterClause1768 (baseVal q)

theorem counterClause1769 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1538)) (countLit q [-11]) (countLit q [-13]) (count1537 q) 1 1 (meaningNeg11 q) (meaningNeg13 q) (meaning1538 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 1538 = true := counterClause1769 (baseVal q)

theorem counterClause1770 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1539)) (countLit q [-14]) (countLit q [-17]) (count1539 q) 1 (meaningNeg17 q) (meaning1539 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1539 = true := counterClause1770 (baseVal q)

theorem counterClause1771 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1539)) (countLit q [-14]) (countLit q [-17]) (count1539 q) 1 (meaningNeg14 q) (meaning1539 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1539 = true := counterClause1771 (baseVal q)

theorem counterClause1772 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1540)) (countLit q [-14]) (countLit q [-17]) (count1539 q) 1 1 (meaningNeg14 q) (meaningNeg17 q) (meaning1540 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 1540 = true := counterClause1772 (baseVal q)

theorem counterClause1773 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-11, -13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -13]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1539)) (literal (valuationOf q) (1541)) (countLit q [-11, -13]) (countLit q [-14, -17]) (count1541 q) 1 (meaning1539 q) (meaning1541 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1541 = true := counterClause1773 (baseVal q)

theorem counterClause1774 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-11, -13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -13]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1540)) (literal (valuationOf q) (1542)) (countLit q [-11, -13]) (countLit q [-14, -17]) (count1541 q) 2 (meaning1540 q) (meaning1542 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1542 = true := counterClause1774 (baseVal q)

theorem counterClause1775 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-11, -13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -13]) (l₂ := [-14, -17])
  have hm := merge_left (literal (valuationOf q) (1537)) (literal (valuationOf q) (1541)) (countLit q [-11, -13]) (countLit q [-14, -17]) (count1541 q) 1 (meaning1537 q) (meaning1541 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1541 = true := counterClause1775 (baseVal q)

theorem counterClause1776 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-11, -13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -13]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1542)) (countLit q [-11, -13]) (countLit q [-14, -17]) (count1541 q) 1 1 (meaning1537 q) (meaning1539 q) (meaning1542 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1539 = false ∨ valuation q 1542 = true := counterClause1776 (baseVal q)

theorem counterClause1777 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-11, -13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -13]) (l₂ := [-14, -17])
  have hm := merge_left (literal (valuationOf q) (1538)) (literal (valuationOf q) (1542)) (countLit q [-11, -13]) (countLit q [-14, -17]) (count1541 q) 2 (meaning1538 q) (meaning1542 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1542 = true := counterClause1777 (baseVal q)

theorem counterClause1778 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-11, -13]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-11, -13]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1543)) (countLit q [-11, -13]) (countLit q [-14, -17]) (count1541 q) 2 1 (meaning1538 q) (meaning1539 q) (meaning1543 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1539 = false ∨ valuation q 1543 = true := counterClause1778 (baseVal q)

theorem counterClause1779 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_right (literal (valuationOf q) (1541)) (literal (valuationOf q) (1545)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 1 (meaning1541 q) (meaning1545 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1545 = true := counterClause1779 (baseVal q)

theorem counterClause1780 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1546 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_right (literal (valuationOf q) (1542)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 2 (meaning1542 q) (meaning1546 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1546 = true := counterClause1780 (baseVal q)

theorem counterClause1781 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_right (literal (valuationOf q) (1543)) (literal (valuationOf q) (1547)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 3 (meaning1543 q) (meaning1547 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1547 = true := counterClause1781 (baseVal q)

theorem counterClause1782 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_left (literal (valuationOf q) (1533)) (literal (valuationOf q) (1545)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 1 (meaning1533 q) (meaning1545 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1545 = true := counterClause1782 (baseVal q)

theorem counterClause1783 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1546 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 1 1 (meaning1533 q) (meaning1541 q) (meaning1546 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1541 = false ∨ valuation q 1546 = true := counterClause1783 (baseVal q)

theorem counterClause1784 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1547)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 1 2 (meaning1533 q) (meaning1542 q) (meaning1547 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1542 = false ∨ valuation q 1547 = true := counterClause1784 (baseVal q)

theorem counterClause1785 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1546 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_left (literal (valuationOf q) (1534)) (literal (valuationOf q) (1546)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 2 (meaning1534 q) (meaning1546 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1546 = true := counterClause1785 (baseVal q)

theorem counterClause1786 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1547)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 2 1 (meaning1534 q) (meaning1541 q) (meaning1547 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1541 = false ∨ valuation q 1547 = true := counterClause1786 (baseVal q)

theorem counterClause1787 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1548)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 2 2 (meaning1534 q) (meaning1542 q) (meaning1548 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1542 = false ∨ valuation q 1548 = true := counterClause1787 (baseVal q)

theorem counterClause1788 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_left (literal (valuationOf q) (1535)) (literal (valuationOf q) (1547)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 3 (meaning1535 q) (meaning1547 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1547 = true := counterClause1788 (baseVal q)

theorem counterClause1789 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1548)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 3 1 (meaning1535 q) (meaning1541 q) (meaning1548 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1541 = false ∨ valuation q 1548 = true := counterClause1789 (baseVal q)

theorem counterClause1790 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1549)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 3 2 (meaning1535 q) (meaning1542 q) (meaning1549 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1542 = false ∨ valuation q 1549 = true := counterClause1790 (baseVal q)

theorem counterClause1791 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_left (literal (valuationOf q) (1536)) (literal (valuationOf q) (1548)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 4 (meaning1536 q) (meaning1548 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1548 = true := counterClause1791 (baseVal q)

theorem counterClause1792 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -8, -9]) + (countLit q [-11, -13, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9]) (l₂ := [-11, -13, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1549)) (countLit q [-3, -4, -8, -9]) (countLit q [-11, -13, -14, -17]) (count1545 q) 4 1 (meaning1536 q) (meaning1541 q) (meaning1549 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1541 = false ∨ valuation q 1549 = true := counterClause1792 (baseVal q)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E260.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112260
