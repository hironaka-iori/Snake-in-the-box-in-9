import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-69, -70]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (countLit q [-69, -70]) (countLit q [-77, -78]) (count1641 q) 1 (meaning1637 q) (meaning1641 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1641 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-69, -70]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (countLit q [-69, -70]) (countLit q [-77, -78]) (count1641 q) 1 1 (meaning1637 q) (meaning1639 q) (meaning1642 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1639 = false ∨ valuation q 1642 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true := by
  have hs : count1641 q = (countLit q [-69, -70]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (countLit q [-69, -70]) (countLit q [-77, -78]) (count1641 q) 1 2 (meaning1637 q) (meaning1640 q) (meaning1643 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1640 = false ∨ valuation q 1643 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-69, -70]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-69, -70]) (countLit q [-77, -78]) (count1641 q) 2 (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1642 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1641 q = (countLit q [-69, -70]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-69, -70]) (countLit q [-77, -78]) (count1641 q) 2 1 (meaning1638 q) (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1641 q = (countLit q [-69, -70]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-69, -70]) (countLit q [-77, -78]) (count1641 q) 2 2 (meaning1638 q) (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 1 (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 2 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 3 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 1 (meaning1634 q) (meaning1645 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1645 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1646)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 1 1 (meaning1634 q) (meaning1641 q) (meaning1646 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1641 = false ∨ valuation q 1646 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 1 2 (meaning1634 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 1 3 (meaning1634 q) (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1649)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 1 4 (meaning1634 q) (meaning1644 q) (meaning1649 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1646)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 2 (meaning1635 q) (meaning1646 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1646 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1647)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 2 1 (meaning1635 q) (meaning1641 q) (meaning1647 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1641 = false ∨ valuation q 1647 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 2 2 (meaning1635 q) (meaning1642 q) (meaning1648 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1642 = false ∨ valuation q 1648 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 2 3 (meaning1635 q) (meaning1643 q) (meaning1649 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1650)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 2 4 (meaning1635 q) (meaning1644 q) (meaning1650 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1647)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 3 (meaning1636 q) (meaning1647 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1647 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1648)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 3 1 (meaning1636 q) (meaning1641 q) (meaning1648 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1641 = false ∨ valuation q 1648 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1649)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 3 2 (meaning1636 q) (meaning1642 q) (meaning1649 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1642 = false ∨ valuation q 1649 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 3 3 (meaning1636 q) (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -70, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -70, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (countLit q [-65, -66, -67]) (countLit q [-69, -70, -77, -78]) (count1645 q) 3 4 (meaning1636 q) (meaning1644 q) (meaning1651 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1644 = false ∨ valuation q 1651 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1652)) (countLit q [-81]) (countLit q [-82]) (count1652 q) 1 (meaningNeg82 q) (meaning1652 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1652 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1652)) (countLit q [-81]) (countLit q [-82]) (count1652 q) 1 (meaningNeg81 q) (meaning1652 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1652 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1653)) (countLit q [-81]) (countLit q [-82]) (count1652 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning1653 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 1653 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1654)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 1 (meaning1652 q) (meaning1654 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1654 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 2 (meaning1653 q) (meaning1655 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1654)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 1 (meaningNeg79 q) (meaning1654 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1654 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1652 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1655)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 1 1 (meaningNeg79 q) (meaning1652 q) (meaning1655 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1652 = false ∨ valuation q 1655 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1656)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 1 2 (meaningNeg79 q) (meaning1653 q) (meaning1656 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1653 = false ∨ valuation q 1656 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E254.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112254
