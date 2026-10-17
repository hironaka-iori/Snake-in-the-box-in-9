import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1640)) (countLit q [-115]) (countLit q [-118]) (count1640 q) 1 (meaningNeg118 q) (meaning1640 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1640 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1640)) (countLit q [-115]) (countLit q [-118]) (count1640 q) 1 (meaningNeg115 q) (meaning1640 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1640 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1641)) (countLit q [-115]) (countLit q [-118]) (count1640 q) 1 1 (meaningNeg115 q) (meaningNeg118 q) (meaning1641 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 118 = true ∨ valuation q 1641 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-111, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-115, -118])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (countLit q [-111, -112]) (countLit q [-115, -118]) (count1642 q) 1 (meaning1640 q) (meaning1642 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-111, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-115, -118])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1643)) (countLit q [-111, -112]) (countLit q [-115, -118]) (count1642 q) 2 (meaning1641 q) (meaning1643 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1643 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-111, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-115, -118])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-111, -112]) (countLit q [-115, -118]) (count1642 q) 1 (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1642 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-111, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-115, -118])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (countLit q [-111, -112]) (countLit q [-115, -118]) (count1642 q) 1 1 (meaning1638 q) (meaning1640 q) (meaning1643 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = false ∨ valuation q 1643 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true := by
  have hs : count1642 q = (countLit q [-111, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-115, -118])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1644)) (countLit q [-111, -112]) (countLit q [-115, -118]) (count1642 q) 1 2 (meaning1638 q) (meaning1641 q) (meaning1644 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1641 = false ∨ valuation q 1644 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-111, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-115, -118])
  have hm := merge_left (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-111, -112]) (countLit q [-115, -118]) (count1642 q) 2 (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1642 q = (countLit q [-111, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-115, -118])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-111, -112]) (countLit q [-115, -118]) (count1642 q) 2 1 (meaning1639 q) (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1642 q = (countLit q [-111, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-115, -118])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-111, -112]) (countLit q [-115, -118]) (count1642 q) 2 2 (meaning1639 q) (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 2 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 3 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_right (literal (valuationOf q) (1645)) (literal (valuationOf q) (1649)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 4 (meaning1645 q) (meaning1649 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1649 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1646)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 1 (meaning1634 q) (meaning1646 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1646 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 1 1 (meaning1634 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 1 2 (meaning1634 q) (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1649)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 1 3 (meaning1634 q) (meaning1644 q) (meaning1649 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1650)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 1 4 (meaning1634 q) (meaning1645 q) (meaning1650 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1645 = false ∨ valuation q 1650 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1647)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 2 (meaning1635 q) (meaning1647 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1647 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 2 1 (meaning1635 q) (meaning1642 q) (meaning1648 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1642 = false ∨ valuation q 1648 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 2 2 (meaning1635 q) (meaning1643 q) (meaning1649 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1650)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 2 3 (meaning1635 q) (meaning1644 q) (meaning1650 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1651)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 2 4 (meaning1635 q) (meaning1645 q) (meaning1651 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1645 = false ∨ valuation q 1651 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1648)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 3 (meaning1636 q) (meaning1648 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1648 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1649)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 3 1 (meaning1636 q) (meaning1642 q) (meaning1649 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1642 = false ∨ valuation q 1649 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 3 2 (meaning1636 q) (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 3 3 (meaning1636 q) (meaning1644 q) (meaning1651 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1644 = false ∨ valuation q 1651 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1652 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1652)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 3 4 (meaning1636 q) (meaning1645 q) (meaning1652 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1645 = false ∨ valuation q 1652 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1650)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 4 1 (meaning1637 q) (meaning1642 q) (meaning1650 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1642 = false ∨ valuation q 1650 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1651)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 4 2 (meaning1637 q) (meaning1643 q) (meaning1651 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1643 = false ∨ valuation q 1651 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1652 = true := by
  have hs : count1646 q = (countLit q [-105, -107, -108, -109]) + (countLit q [-111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -107, -108, -109]) (l₂ := [-111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1652)) (countLit q [-105, -107, -108, -109]) (countLit q [-111, -112, -115, -118]) (count1646 q) 4 3 (meaning1637 q) (meaning1644 q) (meaning1652 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1644 = false ∨ valuation q 1652 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E104.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112104
