import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-112, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1643)) (countLit q [-112, -113]) (countLit q [-115, -117]) (count1642 q) 2 (meaning1641 q) (meaning1643 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1643 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-112, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-112, -113]) (countLit q [-115, -117]) (count1642 q) 1 (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1642 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-112, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (countLit q [-112, -113]) (countLit q [-115, -117]) (count1642 q) 1 1 (meaning1638 q) (meaning1640 q) (meaning1643 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = false ∨ valuation q 1643 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true := by
  have hs : count1642 q = (countLit q [-112, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1644)) (countLit q [-112, -113]) (countLit q [-115, -117]) (count1642 q) 1 2 (meaning1638 q) (meaning1641 q) (meaning1644 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1641 = false ∨ valuation q 1644 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-112, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-112, -113]) (countLit q [-115, -117]) (count1642 q) 2 (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1642 q = (countLit q [-112, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-112, -113]) (countLit q [-115, -117]) (count1642 q) 2 1 (meaning1639 q) (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1642 q = (countLit q [-112, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-112, -113]) (countLit q [-115, -117]) (count1642 q) 2 2 (meaning1639 q) (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 1 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 2 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 3 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1645)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 4 (meaning1645 q) (meaning1649 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1649 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1646)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 1 (meaning1634 q) (meaning1646 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1646 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 1 1 (meaning1634 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 1 2 (meaning1634 q) (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 1 3 (meaning1634 q) (meaning1644 q) (meaning1649 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1650)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 1 4 (meaning1634 q) (meaning1645 q) (meaning1650 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1645 = false ∨ valuation q 1650 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1647)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 2 (meaning1635 q) (meaning1647 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1647 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 2 1 (meaning1635 q) (meaning1642 q) (meaning1648 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1642 = false ∨ valuation q 1648 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 2 2 (meaning1635 q) (meaning1643 q) (meaning1649 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1650)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 2 3 (meaning1635 q) (meaning1644 q) (meaning1650 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1651)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 2 4 (meaning1635 q) (meaning1645 q) (meaning1651 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1645 = false ∨ valuation q 1651 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1648)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 3 (meaning1636 q) (meaning1648 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1648 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 3 1 (meaning1636 q) (meaning1642 q) (meaning1649 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1642 = false ∨ valuation q 1649 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 3 2 (meaning1636 q) (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 3 3 (meaning1636 q) (meaning1644 q) (meaning1651 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1644 = false ∨ valuation q 1651 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1649)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 4 (meaning1637 q) (meaning1649 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1649 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1650)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 4 1 (meaning1637 q) (meaning1642 q) (meaning1650 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1642 = false ∨ valuation q 1650 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-104, -107, -109, -110]) + (countLit q [-112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -107, -109, -110]) (l₂ := [-112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1651)) (countLit q [-104, -107, -109, -110]) (countLit q [-112, -113, -115, -117]) (count1646 q) 4 2 (meaning1637 q) (meaning1643 q) (meaning1651 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1643 = false ∨ valuation q 1651 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1657)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 4 (meaning1649 q) (meaning1657 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1657 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1657)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 1 3 (meaning1623 q) (meaning1648 q) (meaning1657 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1648 = false ∨ valuation q 1657 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1658)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 1 4 (meaning1623 q) (meaning1649 q) (meaning1658 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1649 = false ∨ valuation q 1658 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1659)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 1 5 (meaning1623 q) (meaning1650 q) (meaning1659 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1650 = false ∨ valuation q 1659 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E110.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112110
