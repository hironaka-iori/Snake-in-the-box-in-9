import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-69, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -73]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (countLit q [-69, -73]) (countLit q [-77, -78]) (count1641 q) 1 (meaning1637 q) (meaning1641 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1641 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-69, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (countLit q [-69, -73]) (countLit q [-77, -78]) (count1641 q) 1 1 (meaning1637 q) (meaning1639 q) (meaning1642 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1639 = false ∨ valuation q 1642 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true := by
  have hs : count1641 q = (countLit q [-69, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (countLit q [-69, -73]) (countLit q [-77, -78]) (count1641 q) 1 2 (meaning1637 q) (meaning1640 q) (meaning1643 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1640 = false ∨ valuation q 1643 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-69, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -73]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-69, -73]) (countLit q [-77, -78]) (count1641 q) 2 (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1642 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1641 q = (countLit q [-69, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-69, -73]) (countLit q [-77, -78]) (count1641 q) 2 1 (meaning1638 q) (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1641 q = (countLit q [-69, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-69, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-69, -73]) (countLit q [-77, -78]) (count1641 q) 2 2 (meaning1638 q) (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 1 (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 2 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 3 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 4 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 1 (meaning1634 q) (meaning1645 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1645 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1646)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 1 1 (meaning1634 q) (meaning1641 q) (meaning1646 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1641 = false ∨ valuation q 1646 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 1 2 (meaning1634 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 1 3 (meaning1634 q) (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1649)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 1 4 (meaning1634 q) (meaning1644 q) (meaning1649 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1646)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 2 (meaning1635 q) (meaning1646 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1646 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1647)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 2 1 (meaning1635 q) (meaning1641 q) (meaning1647 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1641 = false ∨ valuation q 1647 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 2 2 (meaning1635 q) (meaning1642 q) (meaning1648 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1642 = false ∨ valuation q 1648 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 2 3 (meaning1635 q) (meaning1643 q) (meaning1649 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1650)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 2 4 (meaning1635 q) (meaning1644 q) (meaning1650 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1647)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 3 (meaning1636 q) (meaning1647 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1647 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1648)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 3 1 (meaning1636 q) (meaning1641 q) (meaning1648 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1641 = false ∨ valuation q 1648 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1649)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 3 2 (meaning1636 q) (meaning1642 q) (meaning1649 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1642 = false ∨ valuation q 1649 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1645 q = (countLit q [-65, -66, -67]) + (countLit q [-69, -73, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-69, -73, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-65, -66, -67]) (countLit q [-69, -73, -77, -78]) (count1645 q) 3 3 (meaning1636 q) (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1652)) (countLit q [-81]) (countLit q [-82]) (count1652 q) 1 (meaningNeg82 q) (meaning1652 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1652 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1652)) (countLit q [-81]) (countLit q [-82]) (count1652 q) 1 (meaningNeg81 q) (meaning1652 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1652 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1653)) (countLit q [-81]) (countLit q [-82]) (count1652 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning1653 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 1653 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1654)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 1 (meaning1652 q) (meaning1654 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1654 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 2 (meaning1653 q) (meaning1655 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1654)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 1 (meaningNeg79 q) (meaning1654 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1654 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1652 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1655)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 1 1 (meaningNeg79 q) (meaning1652 q) (meaning1655 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1652 = false ∨ valuation q 1655 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true := by
  have hs : count1654 q = (countLit q [-79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1656)) (countLit q [-79]) (countLit q [-81, -82]) (count1654 q) 1 2 (meaningNeg79 q) (meaning1653 q) (meaning1656 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1653 = false ∨ valuation q 1656 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E258.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112258
