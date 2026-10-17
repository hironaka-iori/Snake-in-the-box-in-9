import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1657)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 4 (meaning1649 q) (meaning1657 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1657 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1658)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 5 (meaning1650 q) (meaning1658 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1658 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_right (literal (valuationOf q) (1651)) (literal (valuationOf q) (1659)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 6 (meaning1651 q) (meaning1659 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1659 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1657)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 1 3 (meaning1623 q) (meaning1648 q) (meaning1657 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1648 = false ∨ valuation q 1657 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1658)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 1 4 (meaning1623 q) (meaning1649 q) (meaning1658 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1649 = false ∨ valuation q 1658 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1659)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 1 5 (meaning1623 q) (meaning1650 q) (meaning1659 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1650 = false ∨ valuation q 1659 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1660)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 1 6 (meaning1623 q) (meaning1651 q) (meaning1660 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1651 = false ∨ valuation q 1660 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1657)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 2 2 (meaning1624 q) (meaning1647 q) (meaning1657 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1647 = false ∨ valuation q 1657 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1658)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 2 3 (meaning1624 q) (meaning1648 q) (meaning1658 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1648 = false ∨ valuation q 1658 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1659)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 2 4 (meaning1624 q) (meaning1649 q) (meaning1659 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1649 = false ∨ valuation q 1659 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1660)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 2 5 (meaning1624 q) (meaning1650 q) (meaning1660 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1650 = false ∨ valuation q 1660 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1661)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 2 6 (meaning1624 q) (meaning1651 q) (meaning1661 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1651 = false ∨ valuation q 1661 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1662)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 2 7 (meaning1624 q) (meaning1652 q) (meaning1662 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1652 = false ∨ valuation q 1662 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1657)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 3 1 (meaning1625 q) (meaning1646 q) (meaning1657 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1646 = false ∨ valuation q 1657 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1658)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 3 2 (meaning1625 q) (meaning1647 q) (meaning1658 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1647 = false ∨ valuation q 1658 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1659)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 3 3 (meaning1625 q) (meaning1648 q) (meaning1659 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1648 = false ∨ valuation q 1659 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1660)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 3 4 (meaning1625 q) (meaning1649 q) (meaning1660 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1649 = false ∨ valuation q 1660 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1661)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 3 5 (meaning1625 q) (meaning1650 q) (meaning1661 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1650 = false ∨ valuation q 1661 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1662)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 3 6 (meaning1625 q) (meaning1651 q) (meaning1662 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1651 = false ∨ valuation q 1662 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1663 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1663)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 3 7 (meaning1625 q) (meaning1652 q) (meaning1663 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1652 = false ∨ valuation q 1663 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1659)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 4 2 (meaning1626 q) (meaning1647 q) (meaning1659 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1647 = false ∨ valuation q 1659 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1660)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 4 3 (meaning1626 q) (meaning1648 q) (meaning1660 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1648 = false ∨ valuation q 1660 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1661)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 4 4 (meaning1626 q) (meaning1649 q) (meaning1661 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1649 = false ∨ valuation q 1661 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1662)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 4 5 (meaning1626 q) (meaning1650 q) (meaning1662 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1650 = false ∨ valuation q 1662 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1663 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1663)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 4 6 (meaning1626 q) (meaning1651 q) (meaning1663 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1651 = false ∨ valuation q 1663 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1659)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 5 1 (meaning1627 q) (meaning1646 q) (meaning1659 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1646 = false ∨ valuation q 1659 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1660)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 5 2 (meaning1627 q) (meaning1647 q) (meaning1660 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1647 = false ∨ valuation q 1660 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1661)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 5 3 (meaning1627 q) (meaning1648 q) (meaning1661 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1648 = false ∨ valuation q 1661 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1662)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 5 4 (meaning1627 q) (meaning1649 q) (meaning1662 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1649 = false ∨ valuation q 1662 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true := by
  have hs : count1654 q = (countLit q [-88, -90, -92, -93, -96, -99, -102]) + (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -93, -96, -99, -102]) (l₂ := [-104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1663)) (countLit q [-88, -90, -92, -93, -96, -99, -102]) (countLit q [-104, -107, -109, -111, -113, -114, -116, -117]) (count1654 q) 5 5 (meaning1627 q) (meaning1650 q) (meaning1663 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1650 = false ∨ valuation q 1663 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1677)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 2 7 (meaning1596 q) (meaning1660 q) (meaning1677 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1660 = false ∨ valuation q 1677 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 2 8 (meaning1596 q) (meaning1661 q) (meaning1678 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1661 = false ∨ valuation q 1678 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E096.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112096
