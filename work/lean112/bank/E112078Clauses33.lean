import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1632)) (countLit q [-92]) (countLit q [-96]) (count1632 q) 1 (meaningNeg92 q) (meaning1632 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1632 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1633)) (countLit q [-92]) (countLit q [-96]) (count1632 q) 1 1 (meaningNeg92 q) (meaningNeg96 q) (meaning1633 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 96 = true ∨ valuation q 1633 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -96])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (countLit q [-90]) (countLit q [-92, -96]) (count1634 q) 1 (meaning1632 q) (meaning1634 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -96])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (countLit q [-90]) (countLit q [-92, -96]) (count1634 q) 2 (meaning1633 q) (meaning1635 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -96])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1634)) (countLit q [-90]) (countLit q [-92, -96]) (count1634 q) 1 (meaningNeg90 q) (meaning1634 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1634 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -96])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1635)) (countLit q [-90]) (countLit q [-92, -96]) (count1634 q) 1 1 (meaningNeg90 q) (meaning1632 q) (meaning1635 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1632 = false ∨ valuation q 1635 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-90]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -96])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1636)) (countLit q [-90]) (countLit q [-92, -96]) (count1634 q) 1 2 (meaningNeg90 q) (meaning1633 q) (meaning1636 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1633 = false ∨ valuation q 1636 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1637)) (countLit q [-97]) (countLit q [-98]) (count1637 q) 1 (meaningNeg98 q) (meaning1637 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1637 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1637)) (countLit q [-97]) (countLit q [-98]) (count1637 q) 1 (meaningNeg97 q) (meaning1637 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1637 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1638)) (countLit q [-97]) (countLit q [-98]) (count1637 q) 1 1 (meaningNeg97 q) (meaningNeg98 q) (meaning1638 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 1638 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-99]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1639)) (countLit q [-99]) (countLit q [-103]) (count1639 q) 1 (meaningNeg103 q) (meaning1639 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1639 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-99]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1639)) (countLit q [-99]) (countLit q [-103]) (count1639 q) 1 (meaningNeg99 q) (meaning1639 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1639 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-99]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1640)) (countLit q [-99]) (countLit q [-103]) (count1639 q) 1 1 (meaningNeg99 q) (meaningNeg103 q) (meaning1640 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 103 = true ∨ valuation q 1640 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-97, -98]) + (countLit q [-99, -103]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-99, -103])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (countLit q [-97, -98]) (countLit q [-99, -103]) (count1641 q) 1 (meaning1639 q) (meaning1641 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-97, -98]) + (countLit q [-99, -103]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-99, -103])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (countLit q [-97, -98]) (countLit q [-99, -103]) (count1641 q) 2 (meaning1640 q) (meaning1642 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-97, -98]) + (countLit q [-99, -103]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-99, -103])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (countLit q [-97, -98]) (countLit q [-99, -103]) (count1641 q) 1 (meaning1637 q) (meaning1641 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1641 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-97, -98]) + (countLit q [-99, -103]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-99, -103])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (countLit q [-97, -98]) (countLit q [-99, -103]) (count1641 q) 1 1 (meaning1637 q) (meaning1639 q) (meaning1642 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1639 = false ∨ valuation q 1642 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true := by
  have hs : count1641 q = (countLit q [-97, -98]) + (countLit q [-99, -103]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-99, -103])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (countLit q [-97, -98]) (countLit q [-99, -103]) (count1641 q) 1 2 (meaning1637 q) (meaning1640 q) (meaning1643 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1640 = false ∨ valuation q 1643 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-97, -98]) + (countLit q [-99, -103]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-99, -103])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-97, -98]) (countLit q [-99, -103]) (count1641 q) 2 (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1642 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1641 q = (countLit q [-97, -98]) + (countLit q [-99, -103]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-99, -103])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-97, -98]) (countLit q [-99, -103]) (count1641 q) 2 1 (meaning1638 q) (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 1 (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 2 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 3 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1646)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 1 1 (meaning1634 q) (meaning1641 q) (meaning1646 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1641 = false ∨ valuation q 1646 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 1 2 (meaning1634 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 1 3 (meaning1634 q) (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1646)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 2 (meaning1635 q) (meaning1646 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1646 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1647)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 2 1 (meaning1635 q) (meaning1641 q) (meaning1647 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1641 = false ∨ valuation q 1647 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 2 2 (meaning1635 q) (meaning1642 q) (meaning1648 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1642 = false ∨ valuation q 1648 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99, -103]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99, -103])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1648)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99, -103]) (count1645 q) 3 1 (meaning1636 q) (meaning1641 q) (meaning1648 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1641 = false ∨ valuation q 1648 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1652)) (countLit q [-105]) (countLit q [-106]) (count1652 q) 1 (meaningNeg106 q) (meaning1652 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1652 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1652)) (countLit q [-105]) (countLit q [-106]) (count1652 q) 1 (meaningNeg105 q) (meaning1652 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1652 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E078.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112078
