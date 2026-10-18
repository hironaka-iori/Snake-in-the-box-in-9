import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1084)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1083 q) 1 1 (meaning1079 q) (meaning1081 q) (meaning1084 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1081 = false ∨ valuation q 1084 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1085 = true := by
  have hs : count1083 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1085)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1083 q) 1 2 (meaning1079 q) (meaning1082 q) (meaning1085 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1082 = false ∨ valuation q 1085 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_left (literal (valuationOf q) (1080)) (literal (valuationOf q) (1084)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1083 q) 2 (meaning1080 q) (meaning1084 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1084 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1085 = true := by
  have hs : count1083 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_two (literal (valuationOf q) (1080)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1085)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1083 q) 2 1 (meaning1080 q) (meaning1081 q) (meaning1085 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1081 = false ∨ valuation q 1085 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1086 = true := by
  have hs : count1083 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_two (literal (valuationOf q) (1080)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1086)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1083 q) 2 2 (meaning1080 q) (meaning1082 q) (meaning1086 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1082 = false ∨ valuation q 1086 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_right (literal (valuationOf q) (1083)) (literal (valuationOf q) (1087)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 1 (meaning1083 q) (meaning1087 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1087 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_right (literal (valuationOf q) (1084)) (literal (valuationOf q) (1088)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 2 (meaning1084 q) (meaning1088 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1088 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1085 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_right (literal (valuationOf q) (1085)) (literal (valuationOf q) (1089)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 3 (meaning1085 q) (meaning1089 q) hs
  change valuationOf q 1085 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1085 = false ∨ valuation q 1089 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_left (literal (valuationOf q) (1075)) (literal (valuationOf q) (1087)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 1 (meaning1075 q) (meaning1087 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1087 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1088)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 1 1 (meaning1075 q) (meaning1083 q) (meaning1088 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1083 = false ∨ valuation q 1088 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1089)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 1 2 (meaning1075 q) (meaning1084 q) (meaning1089 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1084 = false ∨ valuation q 1089 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1090)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 1 3 (meaning1075 q) (meaning1085 q) (meaning1090 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1085 = false ∨ valuation q 1090 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1091)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 1 4 (meaning1075 q) (meaning1086 q) (meaning1091 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1086 = false ∨ valuation q 1091 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_left (literal (valuationOf q) (1076)) (literal (valuationOf q) (1088)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 2 (meaning1076 q) (meaning1088 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1088 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1089)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 2 1 (meaning1076 q) (meaning1083 q) (meaning1089 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1083 = false ∨ valuation q 1089 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1090)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 2 2 (meaning1076 q) (meaning1084 q) (meaning1090 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1084 = false ∨ valuation q 1090 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1091)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 2 3 (meaning1076 q) (meaning1085 q) (meaning1091 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1085 = false ∨ valuation q 1091 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1092 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1092)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 2 4 (meaning1076 q) (meaning1086 q) (meaning1092 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1086 = false ∨ valuation q 1092 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_left (literal (valuationOf q) (1077)) (literal (valuationOf q) (1089)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 3 (meaning1077 q) (meaning1089 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1089 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1090)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 3 1 (meaning1077 q) (meaning1083 q) (meaning1090 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1083 = false ∨ valuation q 1090 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-111, -113, -116, -118]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -116, -118]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1091)) (countLit q [-111, -113, -116, -118]) (countLit q [-120, -122, -124, -126]) (count1087 q) 3 2 (meaning1077 q) (meaning1084 q) (meaning1091 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1084 = false ∨ valuation q 1091 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1089 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_right (literal (valuationOf q) (1089)) (literal (valuationOf q) (1097)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 3 (meaning1089 q) (meaning1097 q) hs
  change valuationOf q 1089 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1089 = false ∨ valuation q 1097 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1090 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_right (literal (valuationOf q) (1090)) (literal (valuationOf q) (1098)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 4 (meaning1090 q) (meaning1098 q) hs
  change valuationOf q 1090 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1090 = false ∨ valuation q 1098 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1095 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_left (literal (valuationOf q) (1063)) (literal (valuationOf q) (1095)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 1 (meaning1063 q) (meaning1095 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1095 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1095 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1096 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1096)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 1 1 (meaning1063 q) (meaning1087 q) (meaning1096 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1087 = false ∨ valuation q 1096 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1097)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 1 2 (meaning1063 q) (meaning1088 q) (meaning1097 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1088 = false ∨ valuation q 1097 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1098)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 1 3 (meaning1063 q) (meaning1089 q) (meaning1098 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1089 = false ∨ valuation q 1098 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1099)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 1 4 (meaning1063 q) (meaning1090 q) (meaning1099 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1090 = false ∨ valuation q 1099 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1101)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 1 6 (meaning1063 q) (meaning1092 q) (meaning1101 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1092 = false ∨ valuation q 1101 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1096 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_left (literal (valuationOf q) (1064)) (literal (valuationOf q) (1096)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 2 (meaning1064 q) (meaning1096 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1096 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1097)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 2 1 (meaning1064 q) (meaning1087 q) (meaning1097 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1087 = false ∨ valuation q 1097 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1098)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 2 2 (meaning1064 q) (meaning1088 q) (meaning1098 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1088 = false ∨ valuation q 1098 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E256.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112256
