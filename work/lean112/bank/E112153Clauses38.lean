import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1058 = true := by
  have hs : count1057 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1058)) (countLit q [-107]) (countLit q [-108]) (count1057 q) 1 1 (meaningNeg107 q) (meaningNeg108 q) (meaning1058 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 1058 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1057 = false ∨ valuationOf q 1059 = true := by
  have hs : count1059 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_right (literal (valuationOf q) (1057)) (literal (valuationOf q) (1059)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1059 q) 1 (meaning1057 q) (meaning1059 q) hs
  change valuationOf q 1057 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1057 = false ∨ valuation q 1059 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1058 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_right (literal (valuationOf q) (1058)) (literal (valuationOf q) (1060)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1059 q) 2 (meaning1058 q) (meaning1060 q) hs
  change valuationOf q 1058 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1058 = false ∨ valuation q 1060 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1055 = false ∨ valuationOf q 1059 = true := by
  have hs : count1059 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1055)) (literal (valuationOf q) (1059)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1059 q) 1 (meaning1055 q) (meaning1059 q) hs
  change valuationOf q 1055 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1055 = false ∨ valuation q 1059 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1055 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_two (literal (valuationOf q) (1055)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1060)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1059 q) 1 1 (meaning1055 q) (meaning1057 q) (meaning1060 q) hs
  change valuationOf q 1055 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1055 = false ∨ valuation q 1057 = false ∨ valuation q 1060 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1055 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1061 = true := by
  have hs : count1059 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_two (literal (valuationOf q) (1055)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1061)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1059 q) 1 2 (meaning1055 q) (meaning1058 q) (meaning1061 q) hs
  change valuationOf q 1055 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1061 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1055 = false ∨ valuation q 1058 = false ∨ valuation q 1061 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1056 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1056)) (literal (valuationOf q) (1060)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1059 q) 2 (meaning1056 q) (meaning1060 q) hs
  change valuationOf q 1056 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1056 = false ∨ valuation q 1060 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1056 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1061 = true := by
  have hs : count1059 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_two (literal (valuationOf q) (1056)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1061)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1059 q) 2 1 (meaning1056 q) (meaning1057 q) (meaning1061 q) hs
  change valuationOf q 1056 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1061 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1056 = false ∨ valuation q 1057 = false ∨ valuation q 1061 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1056 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1062 = true := by
  have hs : count1059 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_two (literal (valuationOf q) (1056)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1062)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1059 q) 2 2 (meaning1056 q) (meaning1058 q) (meaning1062 q) hs
  change valuationOf q 1056 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1062 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1056 = false ∨ valuation q 1058 = false ∨ valuation q 1062 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1059 = false ∨ valuationOf q 1063 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1059)) (literal (valuationOf q) (1063)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 1 (meaning1059 q) (meaning1063 q) hs
  change valuationOf q 1059 = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1059 = false ∨ valuation q 1063 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1060 = false ∨ valuationOf q 1064 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1060)) (literal (valuationOf q) (1064)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 2 (meaning1060 q) (meaning1064 q) hs
  change valuationOf q 1060 = false ∨ valuationOf q 1064 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1060 = false ∨ valuation q 1064 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1061 = false ∨ valuationOf q 1065 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1061)) (literal (valuationOf q) (1065)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 3 (meaning1061 q) (meaning1065 q) hs
  change valuationOf q 1061 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1061 = false ∨ valuation q 1065 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1062 = false ∨ valuationOf q 1066 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1062)) (literal (valuationOf q) (1066)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 4 (meaning1062 q) (meaning1066 q) hs
  change valuationOf q 1062 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1062 = false ∨ valuation q 1066 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1063 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1051)) (literal (valuationOf q) (1063)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 1 (meaning1051 q) (meaning1063 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1063 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1064 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1064)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 1 1 (meaning1051 q) (meaning1059 q) (meaning1064 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1064 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1059 = false ∨ valuation q 1064 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1065 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1065)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 1 2 (meaning1051 q) (meaning1060 q) (meaning1065 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1060 = false ∨ valuation q 1065 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1066 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1066)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 1 3 (meaning1051 q) (meaning1061 q) (meaning1066 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1061 = false ∨ valuation q 1066 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1067)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 1 4 (meaning1051 q) (meaning1062 q) (meaning1067 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1062 = false ∨ valuation q 1067 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1064 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1052)) (literal (valuationOf q) (1064)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 2 (meaning1052 q) (meaning1064 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1064 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1064 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1065 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1065)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 2 1 (meaning1052 q) (meaning1059 q) (meaning1065 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1059 = false ∨ valuation q 1065 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1066 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1066)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 2 2 (meaning1052 q) (meaning1060 q) (meaning1066 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1060 = false ∨ valuation q 1066 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1067)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 2 3 (meaning1052 q) (meaning1061 q) (meaning1067 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1061 = false ∨ valuation q 1067 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1068)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 2 4 (meaning1052 q) (meaning1062 q) (meaning1068 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1062 = false ∨ valuation q 1068 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1065 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1053)) (literal (valuationOf q) (1065)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 3 (meaning1053 q) (meaning1065 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1065 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1066 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1066)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 3 1 (meaning1053 q) (meaning1059 q) (meaning1066 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1059 = false ∨ valuation q 1066 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1067)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 3 2 (meaning1053 q) (meaning1060 q) (meaning1067 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1060 = false ∨ valuation q 1067 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1068)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 3 3 (meaning1053 q) (meaning1061 q) (meaning1068 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1061 = false ∨ valuation q 1068 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1069)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 3 4 (meaning1053 q) (meaning1062 q) (meaning1069 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1062 = false ∨ valuation q 1069 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1054 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1054)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1067)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 4 1 (meaning1054 q) (meaning1059 q) (meaning1067 q) hs
  change valuationOf q 1054 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1054 = false ∨ valuation q 1059 = false ∨ valuation q 1067 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1054 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1054)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1068)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 4 2 (meaning1054 q) (meaning1060 q) (meaning1068 q) hs
  change valuationOf q 1054 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1054 = false ∨ valuation q 1060 = false ∨ valuation q 1068 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1054 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1069 = true := by
  have hs : count1063 q = (countLit q [-94, -96, -99, -100]) + (countLit q [-103, -105, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100]) (l₂ := [-103, -105, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1054)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1069)) (countLit q [-94, -96, -99, -100]) (countLit q [-103, -105, -107, -108]) (count1063 q) 4 3 (meaning1054 q) (meaning1061 q) (meaning1069 q) hs
  change valuationOf q 1054 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1054 = false ∨ valuation q 1061 = false ∨ valuation q 1069 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1071 = true := by
  have hs : count1071 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1071)) (countLit q [-111]) (countLit q [-112]) (count1071 q) 1 (meaningNeg112 q) (meaning1071 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1071 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1071 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E153.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112153
