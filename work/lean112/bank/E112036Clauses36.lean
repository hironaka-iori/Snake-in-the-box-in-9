import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1635 = true := by
  have hs : count1635 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1635)) (countLit q [-47]) (countLit q [-50]) (count1635 q) 1 (meaningNeg47 q) (meaning1635 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1635 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 50 = true ∨ valuationOf q 1636 = true := by
  have hs : count1635 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (1636)) (countLit q [-47]) (countLit q [-50]) (count1635 q) 1 1 (meaningNeg47 q) (meaningNeg50 q) (meaning1636 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 1636 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1637)) (countLit q [-52]) (countLit q [-54]) (count1637 q) 1 (meaningNeg54 q) (meaning1637 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1637 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1637)) (countLit q [-52]) (countLit q [-54]) (count1637 q) 1 (meaningNeg52 q) (meaning1637 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1637 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1638)) (countLit q [-52]) (countLit q [-54]) (count1637 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning1638 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 1638 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-47, -50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-52, -54])
  have hm := merge_right (literal (valuationOf q) (1637)) (literal (valuationOf q) (1639)) (countLit q [-47, -50]) (countLit q [-52, -54]) (count1639 q) 1 (meaning1637 q) (meaning1639 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1639 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-47, -50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-52, -54])
  have hm := merge_right (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (countLit q [-47, -50]) (countLit q [-52, -54]) (count1639 q) 2 (meaning1638 q) (meaning1640 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-47, -50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-52, -54])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1639)) (countLit q [-47, -50]) (countLit q [-52, -54]) (count1639 q) 1 (meaning1635 q) (meaning1639 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1639 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-47, -50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-52, -54])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1637)) (literal (valuationOf q) (1640)) (countLit q [-47, -50]) (countLit q [-52, -54]) (count1639 q) 1 1 (meaning1635 q) (meaning1637 q) (meaning1640 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1637 = false ∨ valuation q 1640 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1641 = true := by
  have hs : count1639 q = (countLit q [-47, -50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-52, -54])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1641)) (countLit q [-47, -50]) (countLit q [-52, -54]) (count1639 q) 1 2 (meaning1635 q) (meaning1638 q) (meaning1641 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1638 = false ∨ valuation q 1641 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-47, -50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-52, -54])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1640)) (countLit q [-47, -50]) (countLit q [-52, -54]) (count1639 q) 2 (meaning1636 q) (meaning1640 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1640 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1641 = true := by
  have hs : count1639 q = (countLit q [-47, -50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-52, -54])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (countLit q [-47, -50]) (countLit q [-52, -54]) (count1639 q) 2 1 (meaning1636 q) (meaning1637 q) (meaning1641 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1637 = false ∨ valuation q 1641 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1639 q = (countLit q [-47, -50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-52, -54])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-47, -50]) (countLit q [-52, -54]) (count1639 q) 2 2 (meaning1636 q) (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1638 = false ∨ valuation q 1642 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1643)) (countLit q [-55]) (countLit q [-56]) (count1643 q) 1 (meaningNeg56 q) (meaning1643 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1643 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1643)) (countLit q [-55]) (countLit q [-56]) (count1643 q) 1 (meaningNeg55 q) (meaning1643 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1643 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1644)) (countLit q [-55]) (countLit q [-56]) (count1643 q) 1 1 (meaningNeg55 q) (meaningNeg56 q) (meaning1644 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 1644 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1645)) (countLit q [-59]) (countLit q [-61]) (count1645 q) 1 (meaningNeg61 q) (meaning1645 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1645 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1645)) (countLit q [-59]) (countLit q [-61]) (count1645 q) 1 (meaningNeg59 q) (meaning1645 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1645 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 61 = true ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (1646)) (countLit q [-59]) (countLit q [-61]) (count1645 q) 1 1 (meaningNeg59 q) (meaningNeg61 q) (meaning1646 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 61 = true ∨ valuation q 1646 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-57]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -61])
  have hm := merge_right (literal (valuationOf q) (1645)) (literal (valuationOf q) (1647)) (countLit q [-57]) (countLit q [-59, -61]) (count1647 q) 1 (meaning1645 q) (meaning1647 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1647 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-57]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -61])
  have hm := merge_right (literal (valuationOf q) (1646)) (literal (valuationOf q) (1648)) (countLit q [-57]) (countLit q [-59, -61]) (count1647 q) 2 (meaning1646 q) (meaning1648 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1648 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-57]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -61])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1647)) (countLit q [-57]) (countLit q [-59, -61]) (count1647 q) 1 (meaningNeg57 q) (meaning1647 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1647 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1645 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-57]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -61])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1648)) (countLit q [-57]) (countLit q [-59, -61]) (count1647 q) 1 1 (meaningNeg57 q) (meaning1645 q) (meaning1648 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1645 = false ∨ valuation q 1648 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1646 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-57]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -61])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1649)) (countLit q [-57]) (countLit q [-59, -61]) (count1647 q) 1 2 (meaningNeg57 q) (meaning1646 q) (meaning1649 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1646 = false ∨ valuation q 1649 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1647)) (literal (valuationOf q) (1650)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 1 (meaning1647 q) (meaning1650 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1650 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1648)) (literal (valuationOf q) (1651)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 2 (meaning1648 q) (meaning1651 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1651 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1652 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1652)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 3 (meaning1649 q) (meaning1652 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1652 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_left (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 1 (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1650 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1651)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 1 1 (meaning1643 q) (meaning1647 q) (meaning1651 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = false ∨ valuation q 1651 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1652 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1652)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 1 2 (meaning1643 q) (meaning1648 q) (meaning1652 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1648 = false ∨ valuation q 1652 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1653 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1653)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 1 3 (meaning1643 q) (meaning1649 q) (meaning1653 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1649 = false ∨ valuation q 1653 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-55, -56]) + (countLit q [-57, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-57, -59, -61])
  have hm := merge_left (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (countLit q [-55, -56]) (countLit q [-57, -59, -61]) (count1650 q) 2 (meaning1644 q) (meaning1651 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1651 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E036.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112036
