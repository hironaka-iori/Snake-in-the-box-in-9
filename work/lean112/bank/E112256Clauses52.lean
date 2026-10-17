import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1099)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 2 3 (meaning1064 q) (meaning1089 q) (meaning1099 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1089 = false ∨ valuation q 1099 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1100)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 2 4 (meaning1064 q) (meaning1090 q) (meaning1100 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1090 = false ∨ valuation q 1100 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1102)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 2 6 (meaning1064 q) (meaning1092 q) (meaning1102 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1092 = false ∨ valuation q 1102 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_left (literal (valuationOf q) (1065)) (literal (valuationOf q) (1097)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 3 (meaning1065 q) (meaning1097 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1097 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1098)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 3 1 (meaning1065 q) (meaning1087 q) (meaning1098 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1087 = false ∨ valuation q 1098 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1099)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 3 2 (meaning1065 q) (meaning1088 q) (meaning1099 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1088 = false ∨ valuation q 1099 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1100)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 3 3 (meaning1065 q) (meaning1089 q) (meaning1100 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1089 = false ∨ valuation q 1100 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1101)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 3 4 (meaning1065 q) (meaning1090 q) (meaning1101 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1090 = false ∨ valuation q 1101 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1102)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 3 5 (meaning1065 q) (meaning1091 q) (meaning1102 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1091 = false ∨ valuation q 1102 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_left (literal (valuationOf q) (1066)) (literal (valuationOf q) (1098)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 4 (meaning1066 q) (meaning1098 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1098 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1099)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 4 1 (meaning1066 q) (meaning1087 q) (meaning1099 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1087 = false ∨ valuation q 1099 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1100)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 4 2 (meaning1066 q) (meaning1088 q) (meaning1100 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1088 = false ∨ valuation q 1100 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1101)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 4 3 (meaning1066 q) (meaning1089 q) (meaning1101 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1089 = false ∨ valuation q 1101 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1102)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 4 4 (meaning1066 q) (meaning1090 q) (meaning1102 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1090 = false ∨ valuation q 1102 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1103)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 4 5 (meaning1066 q) (meaning1091 q) (meaning1103 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1091 = false ∨ valuation q 1103 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_left (literal (valuationOf q) (1067)) (literal (valuationOf q) (1099)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 5 (meaning1067 q) (meaning1099 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1099 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1101)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 5 2 (meaning1067 q) (meaning1088 q) (meaning1101 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1088 = false ∨ valuation q 1101 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1102)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 5 3 (meaning1067 q) (meaning1089 q) (meaning1102 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1089 = false ∨ valuation q 1102 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1103)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 5 4 (meaning1067 q) (meaning1090 q) (meaning1103 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1090 = false ∨ valuation q 1103 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1102)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 6 2 (meaning1068 q) (meaning1088 q) (meaning1102 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1088 = false ∨ valuation q 1102 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1103)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 6 3 (meaning1068 q) (meaning1089 q) (meaning1103 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1089 = false ∨ valuation q 1103 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1103)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 7 2 (meaning1069 q) (meaning1088 q) (meaning1103 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1088 = false ∨ valuation q 1103 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) + (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-93, -96, -101, -103, -105, -106, -108, -109]) (l₂ := [-111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1104)) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109]) (countLit q [-111, -113, -116, -118, -120, -122, -124, -126]) (count1095 q) 7 3 (meaning1069 q) (meaning1089 q) (meaning1104 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1089 = false ∨ valuation q 1104 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1115 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1115)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 2 3 (meaning1033 q) (meaning1097 q) (meaning1115 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1115 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1097 = false ∨ valuation q 1115 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1116 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1116)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 2 4 (meaning1033 q) (meaning1098 q) (meaning1116 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1116 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1098 = false ∨ valuation q 1116 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1117 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1117)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 2 5 (meaning1033 q) (meaning1099 q) (meaning1117 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1117 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1099 = false ∨ valuation q 1117 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1118)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 2 6 (meaning1033 q) (meaning1100 q) (meaning1118 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1100 = false ∨ valuation q 1118 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1116 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1116)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 3 3 (meaning1034 q) (meaning1097 q) (meaning1116 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1116 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1097 = false ∨ valuation q 1116 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1117 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1117)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 3 4 (meaning1034 q) (meaning1098 q) (meaning1117 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1117 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1098 = false ∨ valuation q 1117 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1118)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 3 5 (meaning1034 q) (meaning1099 q) (meaning1118 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1099 = false ∨ valuation q 1118 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1119)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 3 6 (meaning1034 q) (meaning1100 q) (meaning1119 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1100 = false ∨ valuation q 1119 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1120)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 3 7 (meaning1034 q) (meaning1101 q) (meaning1120 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1101 = false ∨ valuation q 1120 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E256.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112256
