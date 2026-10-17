import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1653 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1653)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 4 4 (meaning1637 q) (meaning1645 q) (meaning1653 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1645 = false ∨ valuation q 1653 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_right (literal (valuationOf q) (1647)) (literal (valuationOf q) (1655)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 2 (meaning1647 q) (meaning1655 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1655 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1656 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_right (literal (valuationOf q) (1648)) (literal (valuationOf q) (1656)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 3 (meaning1648 q) (meaning1656 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1656 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1657)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 4 (meaning1649 q) (meaning1657 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1657 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1658)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 5 (meaning1650 q) (meaning1658 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1658 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_right (literal (valuationOf q) (1651)) (literal (valuationOf q) (1659)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 6 (meaning1651 q) (meaning1659 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1659 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1656 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1656)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 1 2 (meaning1623 q) (meaning1647 q) (meaning1656 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1647 = false ∨ valuation q 1656 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1657)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 1 3 (meaning1623 q) (meaning1648 q) (meaning1657 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1648 = false ∨ valuation q 1657 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1658)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 1 4 (meaning1623 q) (meaning1649 q) (meaning1658 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1649 = false ∨ valuation q 1658 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1659)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 1 5 (meaning1623 q) (meaning1650 q) (meaning1659 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1650 = false ∨ valuation q 1659 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1660)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 1 6 (meaning1623 q) (meaning1651 q) (meaning1660 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1651 = false ∨ valuation q 1660 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1661)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 1 7 (meaning1623 q) (meaning1652 q) (meaning1661 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1652 = false ∨ valuation q 1661 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1662)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 1 8 (meaning1623 q) (meaning1653 q) (meaning1662 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1653 = false ∨ valuation q 1662 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1656 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1656)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 2 1 (meaning1624 q) (meaning1646 q) (meaning1656 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1646 = false ∨ valuation q 1656 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1657)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 2 2 (meaning1624 q) (meaning1647 q) (meaning1657 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1647 = false ∨ valuation q 1657 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1658)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 2 3 (meaning1624 q) (meaning1648 q) (meaning1658 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1648 = false ∨ valuation q 1658 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1659)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 2 4 (meaning1624 q) (meaning1649 q) (meaning1659 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1649 = false ∨ valuation q 1659 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1660)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 2 5 (meaning1624 q) (meaning1650 q) (meaning1660 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1650 = false ∨ valuation q 1660 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1661)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 2 6 (meaning1624 q) (meaning1651 q) (meaning1661 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1651 = false ∨ valuation q 1661 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1662)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 2 7 (meaning1624 q) (meaning1652 q) (meaning1662 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1652 = false ∨ valuation q 1662 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1658)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 3 2 (meaning1625 q) (meaning1647 q) (meaning1658 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1647 = false ∨ valuation q 1658 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1659)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 3 3 (meaning1625 q) (meaning1648 q) (meaning1659 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1648 = false ∨ valuation q 1659 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1660)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 3 4 (meaning1625 q) (meaning1649 q) (meaning1660 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1649 = false ∨ valuation q 1660 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1661)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 3 5 (meaning1625 q) (meaning1650 q) (meaning1661 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1650 = false ∨ valuation q 1661 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1662)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 3 6 (meaning1625 q) (meaning1651 q) (meaning1662 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1651 = false ∨ valuation q 1662 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1663 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1663)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 3 7 (meaning1625 q) (meaning1652 q) (meaning1663 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1652 = false ∨ valuation q 1663 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1659)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 4 2 (meaning1626 q) (meaning1647 q) (meaning1659 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1647 = false ∨ valuation q 1659 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1660)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 4 3 (meaning1626 q) (meaning1648 q) (meaning1660 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1648 = false ∨ valuation q 1660 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1661)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 4 4 (meaning1626 q) (meaning1649 q) (meaning1661 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1649 = false ∨ valuation q 1661 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1662)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 4 5 (meaning1626 q) (meaning1650 q) (meaning1662 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1650 = false ∨ valuation q 1662 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1663 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1663)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 4 6 (meaning1626 q) (meaning1651 q) (meaning1663 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1651 = false ∨ valuation q 1663 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1660)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 5 2 (meaning1627 q) (meaning1647 q) (meaning1660 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1647 = false ∨ valuation q 1660 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E104.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112104
