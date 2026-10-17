import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1071 = true := by
  have hs : count1071 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1071)) (countLit q [-111]) (countLit q [-112]) (count1071 q) 1 (meaningNeg111 q) (meaning1071 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1071 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1071 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1072 = true := by
  have hs : count1071 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1072)) (countLit q [-111]) (countLit q [-112]) (count1071 q) 1 1 (meaningNeg111 q) (meaningNeg112 q) (meaning1072 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1072 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 1072 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1073 = true := by
  have hs : count1073 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_right (literal (valuationOf q) (-115)) (literal (valuationOf q) (1073)) (countLit q [-113]) (countLit q [-115]) (count1073 q) 1 (meaningNeg115 q) (meaning1073 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1073 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1073 = true := by
  have hs : count1073 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1073)) (countLit q [-113]) (countLit q [-115]) (count1073 q) 1 (meaningNeg113 q) (meaning1073 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1073 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 115 = true ∨ valuationOf q 1074 = true := by
  have hs : count1073 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-115)) (literal (valuationOf q) (1074)) (countLit q [-113]) (countLit q [-115]) (count1073 q) 1 1 (meaningNeg113 q) (meaningNeg115 q) (meaning1074 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 115)) = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 115 = true ∨ valuation q 1074 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1073 = false ∨ valuationOf q 1075 = true := by
  have hs : count1075 q = (countLit q [-111, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -115])
  have hm := merge_right (literal (valuationOf q) (1073)) (literal (valuationOf q) (1075)) (countLit q [-111, -112]) (countLit q [-113, -115]) (count1075 q) 1 (meaning1073 q) (meaning1075 q) hs
  change valuationOf q 1073 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1073 = false ∨ valuation q 1075 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1076 = true := by
  have hs : count1075 q = (countLit q [-111, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -115])
  have hm := merge_right (literal (valuationOf q) (1074)) (literal (valuationOf q) (1076)) (countLit q [-111, -112]) (countLit q [-113, -115]) (count1075 q) 2 (meaning1074 q) (meaning1076 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1076 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1075 = true := by
  have hs : count1075 q = (countLit q [-111, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -115])
  have hm := merge_left (literal (valuationOf q) (1071)) (literal (valuationOf q) (1075)) (countLit q [-111, -112]) (countLit q [-113, -115]) (count1075 q) 1 (meaning1071 q) (meaning1075 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1075 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1076 = true := by
  have hs : count1075 q = (countLit q [-111, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1071)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1076)) (countLit q [-111, -112]) (countLit q [-113, -115]) (count1075 q) 1 1 (meaning1071 q) (meaning1073 q) (meaning1076 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1073 = false ∨ valuation q 1076 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1077 = true := by
  have hs : count1075 q = (countLit q [-111, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1071)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1077)) (countLit q [-111, -112]) (countLit q [-113, -115]) (count1075 q) 1 2 (meaning1071 q) (meaning1074 q) (meaning1077 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1074 = false ∨ valuation q 1077 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1076 = true := by
  have hs : count1075 q = (countLit q [-111, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -115])
  have hm := merge_left (literal (valuationOf q) (1072)) (literal (valuationOf q) (1076)) (countLit q [-111, -112]) (countLit q [-113, -115]) (count1075 q) 2 (meaning1072 q) (meaning1076 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1076 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1077 = true := by
  have hs : count1075 q = (countLit q [-111, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1077)) (countLit q [-111, -112]) (countLit q [-113, -115]) (count1075 q) 2 1 (meaning1072 q) (meaning1073 q) (meaning1077 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1073 = false ∨ valuation q 1077 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1078 = true := by
  have hs : count1075 q = (countLit q [-111, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1078)) (countLit q [-111, -112]) (countLit q [-113, -115]) (count1075 q) 2 2 (meaning1072 q) (meaning1074 q) (meaning1078 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1078 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1074 = false ∨ valuation q 1078 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1079 = true := by
  have hs : count1079 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1079)) (countLit q [-117]) (countLit q [-118]) (count1079 q) 1 (meaningNeg118 q) (meaning1079 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1079 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1079 = true := by
  have hs : count1079 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-117)) (literal (valuationOf q) (1079)) (countLit q [-117]) (countLit q [-118]) (count1079 q) 1 (meaningNeg117 q) (meaning1079 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1079 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1080 = true := by
  have hs : count1079 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-117)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1080)) (countLit q [-117]) (countLit q [-118]) (count1079 q) 1 1 (meaningNeg117 q) (meaningNeg118 q) (meaning1080 q) hs
  change (! (valuationOf q 117)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1080 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 1080 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1081 = true := by
  have hs : count1081 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1081)) (countLit q [-121]) (countLit q [-123]) (count1081 q) 1 (meaningNeg123 q) (meaning1081 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1081 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 1081 = true := by
  have hs : count1081 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_left (literal (valuationOf q) (-121)) (literal (valuationOf q) (1081)) (countLit q [-121]) (countLit q [-123]) (count1081 q) 1 (meaningNeg121 q) (meaning1081 q) hs
  change (! (valuationOf q 121)) = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 1081 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 123 = true ∨ valuationOf q 1082 = true := by
  have hs : count1081 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_two (literal (valuationOf q) (-121)) (literal (valuationOf q) (-123)) (literal (valuationOf q) (1082)) (countLit q [-121]) (countLit q [-123]) (count1081 q) 1 1 (meaningNeg121 q) (meaningNeg123 q) (meaning1082 q) hs
  change (! (valuationOf q 121)) = false ∨ (! (valuationOf q 123)) = false ∨ valuationOf q 1082 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 123 = true ∨ valuation q 1082 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1081 = false ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-117, -118]) + (countLit q [-121, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -118]) (l₂ := [-121, -123])
  have hm := merge_right (literal (valuationOf q) (1081)) (literal (valuationOf q) (1083)) (countLit q [-117, -118]) (countLit q [-121, -123]) (count1083 q) 1 (meaning1081 q) (meaning1083 q) hs
  change valuationOf q 1081 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1081 = false ∨ valuation q 1083 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1082 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-117, -118]) + (countLit q [-121, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -118]) (l₂ := [-121, -123])
  have hm := merge_right (literal (valuationOf q) (1082)) (literal (valuationOf q) (1084)) (countLit q [-117, -118]) (countLit q [-121, -123]) (count1083 q) 2 (meaning1082 q) (meaning1084 q) hs
  change valuationOf q 1082 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1082 = false ∨ valuation q 1084 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-117, -118]) + (countLit q [-121, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -118]) (l₂ := [-121, -123])
  have hm := merge_left (literal (valuationOf q) (1079)) (literal (valuationOf q) (1083)) (countLit q [-117, -118]) (countLit q [-121, -123]) (count1083 q) 1 (meaning1079 q) (meaning1083 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1083 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-117, -118]) + (countLit q [-121, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -118]) (l₂ := [-121, -123])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1084)) (countLit q [-117, -118]) (countLit q [-121, -123]) (count1083 q) 1 1 (meaning1079 q) (meaning1081 q) (meaning1084 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1081 = false ∨ valuation q 1084 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1085 = true := by
  have hs : count1083 q = (countLit q [-117, -118]) + (countLit q [-121, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -118]) (l₂ := [-121, -123])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1085)) (countLit q [-117, -118]) (countLit q [-121, -123]) (count1083 q) 1 2 (meaning1079 q) (meaning1082 q) (meaning1085 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1082 = false ∨ valuation q 1085 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-117, -118]) + (countLit q [-121, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -118]) (l₂ := [-121, -123])
  have hm := merge_left (literal (valuationOf q) (1080)) (literal (valuationOf q) (1084)) (countLit q [-117, -118]) (countLit q [-121, -123]) (count1083 q) 2 (meaning1080 q) (meaning1084 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1084 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1085 = true := by
  have hs : count1083 q = (countLit q [-117, -118]) + (countLit q [-121, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -118]) (l₂ := [-121, -123])
  have hm := merge_two (literal (valuationOf q) (1080)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1085)) (countLit q [-117, -118]) (countLit q [-121, -123]) (count1083 q) 2 1 (meaning1080 q) (meaning1081 q) (meaning1085 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1081 = false ∨ valuation q 1085 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1086 = true := by
  have hs : count1083 q = (countLit q [-117, -118]) + (countLit q [-121, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -118]) (l₂ := [-121, -123])
  have hm := merge_two (literal (valuationOf q) (1080)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1086)) (countLit q [-117, -118]) (countLit q [-121, -123]) (count1083 q) 2 2 (meaning1080 q) (meaning1082 q) (meaning1086 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1082 = false ∨ valuation q 1086 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1083)) (literal (valuationOf q) (1087)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 1 (meaning1083 q) (meaning1087 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1087 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1084)) (literal (valuationOf q) (1088)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 2 (meaning1084 q) (meaning1088 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1088 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1085 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1085)) (literal (valuationOf q) (1089)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 3 (meaning1085 q) (meaning1089 q) hs
  change valuationOf q 1085 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1085 = false ∨ valuation q 1089 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1086 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1086)) (literal (valuationOf q) (1090)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 4 (meaning1086 q) (meaning1090 q) hs
  change valuationOf q 1086 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1086 = false ∨ valuation q 1090 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_left (literal (valuationOf q) (1075)) (literal (valuationOf q) (1087)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 1 (meaning1075 q) (meaning1087 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1087 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E153.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112153
