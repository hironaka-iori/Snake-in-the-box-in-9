import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1090)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 3 1 (meaning1077 q) (meaning1083 q) (meaning1090 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1083 = false ∨ valuation q 1090 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1091)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 3 2 (meaning1077 q) (meaning1084 q) (meaning1091 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1084 = false ∨ valuation q 1091 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1092 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1092)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 3 3 (meaning1077 q) (meaning1085 q) (meaning1092 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1085 = false ∨ valuation q 1092 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1091)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 4 1 (meaning1078 q) (meaning1083 q) (meaning1091 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1083 = false ∨ valuation q 1091 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1092 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1092)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 4 2 (meaning1078 q) (meaning1084 q) (meaning1092 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1084 = false ∨ valuation q 1092 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1093 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1093)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 4 3 (meaning1078 q) (meaning1085 q) (meaning1093 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1093 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1085 = false ∨ valuation q 1093 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1089 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1089)) (literal (valuationOf q) (1097)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 3 (meaning1089 q) (meaning1097 q) hs
  change valuationOf q 1089 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1089 = false ∨ valuation q 1097 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1090 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1090)) (literal (valuationOf q) (1098)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 4 (meaning1090 q) (meaning1098 q) hs
  change valuationOf q 1090 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1090 = false ∨ valuation q 1098 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1091 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1091)) (literal (valuationOf q) (1099)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 5 (meaning1091 q) (meaning1099 q) hs
  change valuationOf q 1091 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1091 = false ∨ valuation q 1099 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1097)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 1 2 (meaning1063 q) (meaning1088 q) (meaning1097 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1088 = false ∨ valuation q 1097 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1098)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 1 3 (meaning1063 q) (meaning1089 q) (meaning1098 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1089 = false ∨ valuation q 1098 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1099)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 1 4 (meaning1063 q) (meaning1090 q) (meaning1099 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1090 = false ∨ valuation q 1099 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1100)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 1 5 (meaning1063 q) (meaning1091 q) (meaning1100 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1091 = false ∨ valuation q 1100 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1097)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 2 1 (meaning1064 q) (meaning1087 q) (meaning1097 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1087 = false ∨ valuation q 1097 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1098)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 2 2 (meaning1064 q) (meaning1088 q) (meaning1098 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1088 = false ∨ valuation q 1098 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1099)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 2 3 (meaning1064 q) (meaning1089 q) (meaning1099 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1089 = false ∨ valuation q 1099 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1100)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 2 4 (meaning1064 q) (meaning1090 q) (meaning1100 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1090 = false ∨ valuation q 1100 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1101)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 2 5 (meaning1064 q) (meaning1091 q) (meaning1101 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1091 = false ∨ valuation q 1101 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1102)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 2 6 (meaning1064 q) (meaning1092 q) (meaning1102 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1092 = false ∨ valuation q 1102 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1103)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 2 7 (meaning1064 q) (meaning1093 q) (meaning1103 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1093 = false ∨ valuation q 1103 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1098)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 3 1 (meaning1065 q) (meaning1087 q) (meaning1098 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1087 = false ∨ valuation q 1098 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1099)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 3 2 (meaning1065 q) (meaning1088 q) (meaning1099 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1088 = false ∨ valuation q 1099 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1100)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 3 3 (meaning1065 q) (meaning1089 q) (meaning1100 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1089 = false ∨ valuation q 1100 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1101)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 3 4 (meaning1065 q) (meaning1090 q) (meaning1101 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1090 = false ∨ valuation q 1101 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1102)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 3 5 (meaning1065 q) (meaning1091 q) (meaning1102 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1091 = false ∨ valuation q 1102 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1103)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 3 6 (meaning1065 q) (meaning1092 q) (meaning1103 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1092 = false ∨ valuation q 1103 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1099)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 4 1 (meaning1066 q) (meaning1087 q) (meaning1099 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1087 = false ∨ valuation q 1099 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1100)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 4 2 (meaning1066 q) (meaning1088 q) (meaning1100 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1088 = false ∨ valuation q 1100 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1101)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 4 3 (meaning1066 q) (meaning1089 q) (meaning1101 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1089 = false ∨ valuation q 1101 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1102)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 4 4 (meaning1066 q) (meaning1090 q) (meaning1102 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1090 = false ∨ valuation q 1102 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1103)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 4 5 (meaning1066 q) (meaning1091 q) (meaning1103 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1091 = false ∨ valuation q 1103 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) + (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -103, -105, -108, -110, -111]) (l₂ := [-113, -115, -117, -119, -122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1100)) (countLit q [-96, -98, -100, -103, -105, -108, -110, -111]) (countLit q [-113, -115, -117, -119, -122, -124, -126, -127]) (count1095 q) 5 1 (meaning1067 q) (meaning1087 q) (meaning1100 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1087 = false ∨ valuation q 1100 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E260.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112260
