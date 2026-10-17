import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1091 = false ∨ valuationOf q 1095 = true := by
  have hs : count1095 q = (countLit q [-103, -105]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1091)) (literal (valuationOf q) (1095)) (countLit q [-103, -105]) (countLit q [-107, -109]) (count1095 q) 1 (meaning1091 q) (meaning1095 q) hs
  change valuationOf q 1091 = false ∨ valuationOf q 1095 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1091 = false ∨ valuation q 1095 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1091 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1096 = true := by
  have hs : count1095 q = (countLit q [-103, -105]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1091)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1096)) (countLit q [-103, -105]) (countLit q [-107, -109]) (count1095 q) 1 1 (meaning1091 q) (meaning1093 q) (meaning1096 q) hs
  change valuationOf q 1091 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1091 = false ∨ valuation q 1093 = false ∨ valuation q 1096 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 1091 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-103, -105]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1091)) (literal (valuationOf q) (1094)) (literal (valuationOf q) (1097)) (countLit q [-103, -105]) (countLit q [-107, -109]) (count1095 q) 1 2 (meaning1091 q) (meaning1094 q) (meaning1097 q) hs
  change valuationOf q 1091 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 1091 = false ∨ valuation q 1094 = false ∨ valuation q 1097 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 1092 = false ∨ valuationOf q 1096 = true := by
  have hs : count1095 q = (countLit q [-103, -105]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1092)) (literal (valuationOf q) (1096)) (countLit q [-103, -105]) (countLit q [-107, -109]) (count1095 q) 2 (meaning1092 q) (meaning1096 q) hs
  change valuationOf q 1092 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 1092 = false ∨ valuation q 1096 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1092 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-103, -105]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1092)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1097)) (countLit q [-103, -105]) (countLit q [-107, -109]) (count1095 q) 2 1 (meaning1092 q) (meaning1093 q) (meaning1097 q) hs
  change valuationOf q 1092 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1092 = false ∨ valuation q 1093 = false ∨ valuation q 1097 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1092 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-103, -105]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1092)) (literal (valuationOf q) (1094)) (literal (valuationOf q) (1098)) (countLit q [-103, -105]) (countLit q [-107, -109]) (count1095 q) 2 2 (meaning1092 q) (meaning1094 q) (meaning1098 q) hs
  change valuationOf q 1092 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1092 = false ∨ valuation q 1094 = false ∨ valuation q 1098 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1095 = false ∨ valuationOf q 1099 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1095)) (literal (valuationOf q) (1099)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 1 (meaning1095 q) (meaning1099 q) hs
  change valuationOf q 1095 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1095 = false ∨ valuation q 1099 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1096 = false ∨ valuationOf q 1100 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1096)) (literal (valuationOf q) (1100)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 2 (meaning1096 q) (meaning1100 q) hs
  change valuationOf q 1096 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1096 = false ∨ valuation q 1100 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1097 = false ∨ valuationOf q 1101 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1097)) (literal (valuationOf q) (1101)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 3 (meaning1097 q) (meaning1101 q) hs
  change valuationOf q 1097 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1097 = false ∨ valuation q 1101 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1098 = false ∨ valuationOf q 1102 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1098)) (literal (valuationOf q) (1102)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 4 (meaning1098 q) (meaning1102 q) hs
  change valuationOf q 1098 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1098 = false ∨ valuation q 1102 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1087 = false ∨ valuationOf q 1099 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1087)) (literal (valuationOf q) (1099)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 1 (meaning1087 q) (meaning1099 q) hs
  change valuationOf q 1087 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1087 = false ∨ valuation q 1099 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1087 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1100 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1087)) (literal (valuationOf q) (1095)) (literal (valuationOf q) (1100)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 1 1 (meaning1087 q) (meaning1095 q) (meaning1100 q) hs
  change valuationOf q 1087 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1087 = false ∨ valuation q 1095 = false ∨ valuation q 1100 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 1087 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1101 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1087)) (literal (valuationOf q) (1096)) (literal (valuationOf q) (1101)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 1 2 (meaning1087 q) (meaning1096 q) (meaning1101 q) hs
  change valuationOf q 1087 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 1087 = false ∨ valuation q 1096 = false ∨ valuation q 1101 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 1087 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1102 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1087)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1102)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 1 3 (meaning1087 q) (meaning1097 q) (meaning1102 q) hs
  change valuationOf q 1087 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 1087 = false ∨ valuation q 1097 = false ∨ valuation q 1102 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1087 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1103 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1087)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1103)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 1 4 (meaning1087 q) (meaning1098 q) (meaning1103 q) hs
  change valuationOf q 1087 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1087 = false ∨ valuation q 1098 = false ∨ valuation q 1103 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1088 = false ∨ valuationOf q 1100 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1088)) (literal (valuationOf q) (1100)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 2 (meaning1088 q) (meaning1100 q) hs
  change valuationOf q 1088 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false ∨ valuation q 1100 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1088 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1101 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1088)) (literal (valuationOf q) (1095)) (literal (valuationOf q) (1101)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 2 1 (meaning1088 q) (meaning1095 q) (meaning1101 q) hs
  change valuationOf q 1088 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false ∨ valuation q 1095 = false ∨ valuation q 1101 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1088 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1102 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1088)) (literal (valuationOf q) (1096)) (literal (valuationOf q) (1102)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 2 2 (meaning1088 q) (meaning1096 q) (meaning1102 q) hs
  change valuationOf q 1088 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false ∨ valuation q 1096 = false ∨ valuation q 1102 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1088 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1103 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1088)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1103)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 2 3 (meaning1088 q) (meaning1097 q) (meaning1103 q) hs
  change valuationOf q 1088 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false ∨ valuation q 1097 = false ∨ valuation q 1103 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1089 = false ∨ valuationOf q 1101 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1089)) (literal (valuationOf q) (1101)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 3 (meaning1089 q) (meaning1101 q) hs
  change valuationOf q 1089 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1089 = false ∨ valuation q 1101 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1089 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1102 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1089)) (literal (valuationOf q) (1095)) (literal (valuationOf q) (1102)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 3 1 (meaning1089 q) (meaning1095 q) (meaning1102 q) hs
  change valuationOf q 1089 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1089 = false ∨ valuation q 1095 = false ∨ valuation q 1102 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1089 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1103 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1089)) (literal (valuationOf q) (1096)) (literal (valuationOf q) (1103)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 3 2 (meaning1089 q) (meaning1096 q) (meaning1103 q) hs
  change valuationOf q 1089 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1089 = false ∨ valuation q 1096 = false ∨ valuation q 1103 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1089 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1104 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1089)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1104)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 3 3 (meaning1089 q) (meaning1097 q) (meaning1104 q) hs
  change valuationOf q 1089 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1089 = false ∨ valuation q 1097 = false ∨ valuation q 1104 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1090 = false ∨ valuationOf q 1102 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1090)) (literal (valuationOf q) (1102)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 4 (meaning1090 q) (meaning1102 q) hs
  change valuationOf q 1090 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1090 = false ∨ valuation q 1102 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1090 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1103 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1090)) (literal (valuationOf q) (1095)) (literal (valuationOf q) (1103)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 4 1 (meaning1090 q) (meaning1095 q) (meaning1103 q) hs
  change valuationOf q 1090 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1090 = false ∨ valuation q 1095 = false ∨ valuation q 1103 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1090 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1104 = true := by
  have hs : count1099 q = (countLit q [-95, -96, -97, -101]) + (countLit q [-103, -105, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101]) (l₂ := [-103, -105, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1090)) (literal (valuationOf q) (1096)) (literal (valuationOf q) (1104)) (countLit q [-95, -96, -97, -101]) (countLit q [-103, -105, -107, -109]) (count1099 q) 4 2 (meaning1090 q) (meaning1096 q) (meaning1104 q) hs
  change valuationOf q 1090 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1090 = false ∨ valuation q 1096 = false ∨ valuation q 1104 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1107 = true := by
  have hs : count1107 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1107)) (countLit q [-112]) (countLit q [-113]) (count1107 q) 1 (meaningNeg113 q) (meaning1107 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1107 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1107 = true := by
  have hs : count1107 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1107)) (countLit q [-112]) (countLit q [-113]) (count1107 q) 1 (meaningNeg112 q) (meaning1107 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1107 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1108 = true := by
  have hs : count1107 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1108)) (countLit q [-112]) (countLit q [-113]) (count1107 q) 1 1 (meaningNeg112 q) (meaningNeg113 q) (meaning1108 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 1108 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1109 = true := by
  have hs : count1109 q = (countLit q [-114]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1109)) (countLit q [-114]) (countLit q [-118]) (count1109 q) 1 (meaningNeg118 q) (meaning1109 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1109 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1109 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1109 = true := by
  have hs : count1109 q = (countLit q [-114]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1109)) (countLit q [-114]) (countLit q [-118]) (count1109 q) 1 (meaningNeg114 q) (meaning1109 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1109 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1109 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1110 = true := by
  have hs : count1109 q = (countLit q [-114]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-114)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1110)) (countLit q [-114]) (countLit q [-118]) (count1109 q) 1 1 (meaningNeg114 q) (meaningNeg118 q) (meaning1110 q) hs
  change (! (valuationOf q 114)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1110 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 118 = true ∨ valuation q 1110 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E057.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112057
