import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1634 = true := by
  have hs : count1632 q = (countLit q [-97, -98]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1634)) (countLit q [-97, -98]) (countLit q [-102, -104]) (count1632 q) 1 2 (meaning1628 q) (meaning1631 q) (meaning1634 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1631 = false ∨ valuation q 1634 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-97, -98]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-102, -104])
  have hm := merge_left (literal (valuationOf q) (1629)) (literal (valuationOf q) (1633)) (countLit q [-97, -98]) (countLit q [-102, -104]) (count1632 q) 2 (meaning1629 q) (meaning1633 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1633 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1632 q = (countLit q [-97, -98]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-97, -98]) (countLit q [-102, -104]) (count1632 q) 2 1 (meaning1629 q) (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1630 = false ∨ valuation q 1634 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1635 = true := by
  have hs : count1632 q = (countLit q [-97, -98]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-102, -104])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1635)) (countLit q [-97, -98]) (countLit q [-102, -104]) (count1632 q) 2 2 (meaning1629 q) (meaning1631 q) (meaning1635 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1631 = false ∨ valuation q 1635 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1636)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 1 (meaning1632 q) (meaning1636 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1636 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1637)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 2 (meaning1633 q) (meaning1637 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1637 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_right (literal (valuationOf q) (1634)) (literal (valuationOf q) (1638)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 3 (meaning1634 q) (meaning1638 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1638 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_left (literal (valuationOf q) (1625)) (literal (valuationOf q) (1636)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 1 (meaning1625 q) (meaning1636 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1636 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1637)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 1 1 (meaning1625 q) (meaning1632 q) (meaning1637 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1632 = false ∨ valuation q 1637 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1638)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 1 2 (meaning1625 q) (meaning1633 q) (meaning1638 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1633 = false ∨ valuation q 1638 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1639 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1639)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 1 3 (meaning1625 q) (meaning1634 q) (meaning1639 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1634 = false ∨ valuation q 1639 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1640 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1635)) (literal (valuationOf q) (1640)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 1 4 (meaning1625 q) (meaning1635 q) (meaning1640 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1635 = false ∨ valuation q 1640 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_left (literal (valuationOf q) (1626)) (literal (valuationOf q) (1637)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 2 (meaning1626 q) (meaning1637 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1637 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1638)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 2 1 (meaning1626 q) (meaning1632 q) (meaning1638 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1632 = false ∨ valuation q 1638 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1639 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1639)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 2 2 (meaning1626 q) (meaning1633 q) (meaning1639 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1633 = false ∨ valuation q 1639 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1640 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1640)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 2 3 (meaning1626 q) (meaning1634 q) (meaning1640 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1634 = false ∨ valuation q 1640 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_left (literal (valuationOf q) (1627)) (literal (valuationOf q) (1638)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 3 (meaning1627 q) (meaning1638 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1638 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1639 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1639)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 3 1 (meaning1627 q) (meaning1632 q) (meaning1639 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1632 = false ∨ valuation q 1639 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1640 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1640)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 3 2 (meaning1627 q) (meaning1633 q) (meaning1640 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1633 = false ∨ valuation q 1640 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1641 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -94]) + (countLit q [-97, -98, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-97, -98, -102, -104])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1641)) (countLit q [-92, -93, -94]) (countLit q [-97, -98, -102, -104]) (count1636 q) 3 3 (meaning1627 q) (meaning1634 q) (meaning1641 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1634 = false ∨ valuation q 1641 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-106]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1643)) (countLit q [-106]) (countLit q [-109]) (count1643 q) 1 (meaningNeg109 q) (meaning1643 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1643 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-106]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1643)) (countLit q [-106]) (countLit q [-109]) (count1643 q) 1 (meaningNeg106 q) (meaning1643 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1643 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-106]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1644)) (countLit q [-106]) (countLit q [-109]) (count1643 q) 1 1 (meaningNeg106 q) (meaningNeg109 q) (meaning1644 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 109 = true ∨ valuation q 1644 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106, -109])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1645)) (countLit q [-105]) (countLit q [-106, -109]) (count1645 q) 1 (meaning1643 q) (meaning1645 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1645 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106, -109])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1646)) (countLit q [-105]) (countLit q [-106, -109]) (count1645 q) 2 (meaning1644 q) (meaning1646 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1646 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106, -109])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1645)) (countLit q [-105]) (countLit q [-106, -109]) (count1645 q) 1 (meaningNeg105 q) (meaning1645 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1645 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1643 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106, -109])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1646)) (countLit q [-105]) (countLit q [-106, -109]) (count1645 q) 1 1 (meaningNeg105 q) (meaning1643 q) (meaning1646 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1643 = false ∨ valuation q 1646 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1648)) (countLit q [-111]) (countLit q [-113]) (count1648 q) 1 (meaningNeg113 q) (meaning1648 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1648 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1648)) (countLit q [-111]) (countLit q [-113]) (count1648 q) 1 (meaningNeg111 q) (meaning1648 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1648 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1649 = true := by
  have hs : count1648 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1649)) (countLit q [-111]) (countLit q [-113]) (count1648 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1649 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1649 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1650)) (countLit q [-115]) (countLit q [-117]) (count1650 q) 1 (meaningNeg117 q) (meaning1650 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1650 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1650)) (countLit q [-115]) (countLit q [-117]) (count1650 q) 1 (meaningNeg115 q) (meaning1650 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1650 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E007.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112007
