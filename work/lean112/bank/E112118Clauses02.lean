import E112118Semantics
import B112E118Inputs
namespace Snake9.Regrowth.E112118
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause65 (q : Nat → Bool) : valuationOf q 1187 = false ∨ valuationOf q 1192 = false ∨ valuationOf q 1196 = true := by
  have hs : count1195 q = (countLit q [-26, -28, -32]) + (countLit q [-33, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -32]) (l₂ := [-33, -34, -35])
  have hm := merge_two (literal (valuationOf q) (1187)) (literal (valuationOf q) (1192)) (literal (valuationOf q) (1196)) (countLit q [-26, -28, -32]) (countLit q [-33, -34, -35]) (count1195 q) 1 1 (meaning1187 q) (meaning1192 q) (meaning1196 q) hs
  change valuationOf q 1187 = false ∨ valuationOf q 1192 = false ∨ valuationOf q 1196 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 1187 = false ∨ valuation q 1192 = false ∨ valuation q 1196 = true := counterClause65 (baseVal q)

theorem counterClause66 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1201 = true := by
  have hs : count1201 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1201)) (countLit q [-41]) (countLit q [-42]) (count1201 q) 1 (meaningNeg42 q) (meaning1201 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1201 = true := counterClause66 (baseVal q)

theorem counterClause67 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1203 = true := by
  have hs : count1203 q = (countLit q [-39]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41, -42])
  have hm := merge_right (literal (valuationOf q) (1201)) (literal (valuationOf q) (1203)) (countLit q [-39]) (countLit q [-41, -42]) (count1203 q) 1 (meaning1201 q) (meaning1203 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1203 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1203 = true := counterClause67 (baseVal q)

theorem counterClause68 (q : Nat → Bool) : valuationOf q 1203 = false ∨ valuationOf q 1211 = true := by
  have hs : count1211 q = (countLit q [-39, -41, -42]) + (countLit q [-43, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -42]) (l₂ := [-43, -47, -48])
  have hm := merge_left (literal (valuationOf q) (1203)) (literal (valuationOf q) (1211)) (countLit q [-39, -41, -42]) (countLit q [-43, -47, -48]) (count1211 q) 1 (meaning1203 q) (meaning1211 q) hs
  change valuationOf q 1203 = false ∨ valuationOf q 1211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 1203 = false ∨ valuation q 1211 = true := counterClause68 (baseVal q)

theorem counterClause69 (q : Nat → Bool) : valuationOf q 1195 = false ∨ valuationOf q 1217 = true := by
  have hs : count1217 q = (countLit q [-26, -28, -32, -33, -34, -35]) + (countLit q [-39, -41, -42, -43, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -32, -33, -34, -35]) (l₂ := [-39, -41, -42, -43, -47, -48])
  have hm := merge_left (literal (valuationOf q) (1195)) (literal (valuationOf q) (1217)) (countLit q [-26, -28, -32, -33, -34, -35]) (countLit q [-39, -41, -42, -43, -47, -48]) (count1217 q) 1 (meaning1195 q) (meaning1217 q) hs
  change valuationOf q 1195 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 1195 = false ∨ valuation q 1217 = true := counterClause69 (baseVal q)

theorem counterClause70 (q : Nat → Bool) : valuationOf q 1195 = false ∨ valuationOf q 1211 = false ∨ valuationOf q 1218 = true := by
  have hs : count1217 q = (countLit q [-26, -28, -32, -33, -34, -35]) + (countLit q [-39, -41, -42, -43, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -32, -33, -34, -35]) (l₂ := [-39, -41, -42, -43, -47, -48])
  have hm := merge_two (literal (valuationOf q) (1195)) (literal (valuationOf q) (1211)) (literal (valuationOf q) (1218)) (countLit q [-26, -28, -32, -33, -34, -35]) (countLit q [-39, -41, -42, -43, -47, -48]) (count1217 q) 1 1 (meaning1195 q) (meaning1211 q) (meaning1218 q) hs
  change valuationOf q 1195 = false ∨ valuationOf q 1211 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 1195 = false ∨ valuation q 1211 = false ∨ valuation q 1218 = true := counterClause70 (baseVal q)

theorem counterClause71 (q : Nat → Bool) : valuationOf q 1196 = false ∨ valuationOf q 1218 = true := by
  have hs : count1217 q = (countLit q [-26, -28, -32, -33, -34, -35]) + (countLit q [-39, -41, -42, -43, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -32, -33, -34, -35]) (l₂ := [-39, -41, -42, -43, -47, -48])
  have hm := merge_left (literal (valuationOf q) (1196)) (literal (valuationOf q) (1218)) (countLit q [-26, -28, -32, -33, -34, -35]) (countLit q [-39, -41, -42, -43, -47, -48]) (count1217 q) 2 (meaning1196 q) (meaning1218 q) hs
  change valuationOf q 1196 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 1196 = false ∨ valuation q 1218 = true := counterClause71 (baseVal q)

theorem counterClause72 (q : Nat → Bool) : valuationOf q 1217 = false ∨ valuationOf q 1224 = true := by
  have hs : count1224 q = (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) + (countLit q [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) (l₂ := [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48])
  have hm := merge_right (literal (valuationOf q) (1217)) (literal (valuationOf q) (1224)) (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) (countLit q [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) (count1224 q) 1 (meaning1217 q) (meaning1224 q) hs
  change valuationOf q 1217 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 1217 = false ∨ valuation q 1224 = true := counterClause72 (baseVal q)

theorem counterClause73 (q : Nat → Bool) : valuationOf q 1218 = false ∨ valuationOf q 1225 = true := by
  have hs : count1224 q = (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) + (countLit q [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) (l₂ := [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48])
  have hm := merge_right (literal (valuationOf q) (1218)) (literal (valuationOf q) (1225)) (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) (countLit q [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) (count1224 q) 2 (meaning1218 q) (meaning1225 q) hs
  change valuationOf q 1218 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 1218 = false ∨ valuation q 1225 = true := counterClause73 (baseVal q)

theorem counterClause74 (q : Nat → Bool) : valuationOf q 1178 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true := by
  have hs : count1224 q = (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) + (countLit q [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) (l₂ := [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48])
  have hm := merge_two (literal (valuationOf q) (1178)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1225)) (countLit q [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]) (countLit q [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]) (count1224 q) 1 1 (meaning1178 q) (meaning1217 q) (meaning1225 q) hs
  change valuationOf q 1178 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 1178 = false ∨ valuation q 1217 = false ∨ valuation q 1225 = true := counterClause74 (baseVal q)

theorem counterClause75 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1231 = true := by
  have hs : count1231 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1231)) (countLit q [-53]) (countLit q [-54]) (count1231 q) 1 (meaningNeg54 q) (meaning1231 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1231 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1231 = true := counterClause75 (baseVal q)

theorem counterClause76 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1233 = true := by
  have hs : count1233 q = (countLit q [-49]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1231)) (literal (valuationOf q) (1233)) (countLit q [-49]) (countLit q [-53, -54]) (count1233 q) 1 (meaning1231 q) (meaning1233 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1233 = true := counterClause76 (baseVal q)

theorem counterClause77 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1241 = true := by
  have hs : count1241 q = (countLit q [-49, -53, -54]) + (countLit q [-55, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-49, -53, -54]) (l₂ := [-55, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1233)) (literal (valuationOf q) (1241)) (countLit q [-49, -53, -54]) (countLit q [-55, -57, -61]) (count1241 q) 1 (meaning1233 q) (meaning1241 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1241 = true := counterClause77 (baseVal q)

theorem counterClause78 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1247 = true := by
  have hs : count1247 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (1247)) (countLit q [-64]) (countLit q [-65]) (count1247 q) 1 (meaningNeg65 q) (meaning1247 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1247 = true := counterClause78 (baseVal q)

theorem counterClause79 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1247 = true := by
  have hs : count1247 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1247)) (countLit q [-64]) (countLit q [-65]) (count1247 q) 1 (meaningNeg64 q) (meaning1247 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1247 = true := counterClause79 (baseVal q)

theorem counterClause80 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1249 = true := by
  have hs : count1249 q = (countLit q [-63]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -65])
  have hm := merge_right (literal (valuationOf q) (1247)) (literal (valuationOf q) (1249)) (countLit q [-63]) (countLit q [-64, -65]) (count1249 q) 1 (meaning1247 q) (meaning1249 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1249 = true := counterClause80 (baseVal q)

theorem counterClause81 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1249 = true := by
  have hs : count1249 q = (countLit q [-63]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -65])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1249)) (countLit q [-63]) (countLit q [-64, -65]) (count1249 q) 1 (meaningNeg63 q) (meaning1249 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1249 = true := counterClause81 (baseVal q)

theorem counterClause82 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1252)) (countLit q [-71]) (countLit q [-73]) (count1252 q) 1 (meaningNeg73 q) (meaning1252 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1252 = true := counterClause82 (baseVal q)

theorem counterClause83 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1252)) (countLit q [-71]) (countLit q [-73]) (count1252 q) 1 (meaningNeg71 q) (meaning1252 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1252 = true := counterClause83 (baseVal q)

theorem counterClause84 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1252)) (literal (valuationOf q) (1254)) (countLit q [-69]) (countLit q [-71, -73]) (count1254 q) 1 (meaning1252 q) (meaning1254 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1254 = true := counterClause84 (baseVal q)

theorem counterClause85 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1254)) (countLit q [-69]) (countLit q [-71, -73]) (count1254 q) 1 (meaningNeg69 q) (meaning1254 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1254 = true := counterClause85 (baseVal q)

theorem counterClause86 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1252 = false ∨ valuationOf q 1255 = true := by
  have hs : count1254 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (1252)) (literal (valuationOf q) (1255)) (countLit q [-69]) (countLit q [-71, -73]) (count1254 q) 1 1 (meaningNeg69 q) (meaning1252 q) (meaning1255 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1252 = false ∨ valuation q 1255 = true := counterClause86 (baseVal q)

theorem counterClause87 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-63, -64, -65]) + (countLit q [-69, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -65]) (l₂ := [-69, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1249)) (literal (valuationOf q) (1257)) (countLit q [-63, -64, -65]) (countLit q [-69, -71, -73]) (count1257 q) 1 (meaning1249 q) (meaning1257 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1257 = true := counterClause87 (baseVal q)

theorem counterClause88 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1254 = false ∨ valuationOf q 1258 = true := by
  have hs : count1257 q = (countLit q [-63, -64, -65]) + (countLit q [-69, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -65]) (l₂ := [-69, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1254)) (literal (valuationOf q) (1258)) (countLit q [-63, -64, -65]) (countLit q [-69, -71, -73]) (count1257 q) 1 1 (meaning1249 q) (meaning1254 q) (meaning1258 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1254 = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1254 = false ∨ valuation q 1258 = true := counterClause88 (baseVal q)

theorem counterClause89 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1259 = true := by
  have hs : count1257 q = (countLit q [-63, -64, -65]) + (countLit q [-69, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -65]) (l₂ := [-69, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1255)) (literal (valuationOf q) (1259)) (countLit q [-63, -64, -65]) (countLit q [-69, -71, -73]) (count1257 q) 1 2 (meaning1249 q) (meaning1255 q) (meaning1259 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1255 = false ∨ valuation q 1259 = true := counterClause89 (baseVal q)

theorem counterClause90 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1264 = true := by
  have hs : count1263 q = (countLit q [-49, -53, -54, -55, -57, -61]) + (countLit q [-63, -64, -65, -69, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-49, -53, -54, -55, -57, -61]) (l₂ := [-63, -64, -65, -69, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1241)) (literal (valuationOf q) (1257)) (literal (valuationOf q) (1264)) (countLit q [-49, -53, -54, -55, -57, -61]) (countLit q [-63, -64, -65, -69, -71, -73]) (count1263 q) 1 1 (meaning1241 q) (meaning1257 q) (meaning1264 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1257 = false ∨ valuation q 1264 = true := counterClause90 (baseVal q)

theorem counterClause91 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1265 = true := by
  have hs : count1263 q = (countLit q [-49, -53, -54, -55, -57, -61]) + (countLit q [-63, -64, -65, -69, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-49, -53, -54, -55, -57, -61]) (l₂ := [-63, -64, -65, -69, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1241)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1265)) (countLit q [-49, -53, -54, -55, -57, -61]) (countLit q [-63, -64, -65, -69, -71, -73]) (count1263 q) 1 2 (meaning1241 q) (meaning1258 q) (meaning1265 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1258 = false ∨ valuation q 1265 = true := counterClause91 (baseVal q)

theorem counterClause92 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1266 = true := by
  have hs : count1263 q = (countLit q [-49, -53, -54, -55, -57, -61]) + (countLit q [-63, -64, -65, -69, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-49, -53, -54, -55, -57, -61]) (l₂ := [-63, -64, -65, -69, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1241)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1266)) (countLit q [-49, -53, -54, -55, -57, -61]) (countLit q [-63, -64, -65, -69, -71, -73]) (count1263 q) 1 3 (meaning1241 q) (meaning1259 q) (meaning1266 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1259 = false ∨ valuation q 1266 = true := counterClause92 (baseVal q)

theorem counterClause93 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-75]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1270)) (countLit q [-75]) (countLit q [-79]) (count1270 q) 1 (meaningNeg79 q) (meaning1270 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1270 = true := counterClause93 (baseVal q)

theorem counterClause94 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-75]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1270)) (countLit q [-75]) (countLit q [-79]) (count1270 q) 1 (meaningNeg75 q) (meaning1270 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1270 = true := counterClause94 (baseVal q)

theorem counterClause95 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1271 = true := by
  have hs : count1270 q = (countLit q [-75]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1271)) (countLit q [-75]) (countLit q [-79]) (count1270 q) 1 1 (meaningNeg75 q) (meaningNeg79 q) (meaning1271 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 79 = true ∨ valuation q 1271 = true := counterClause95 (baseVal q)

theorem counterClause96 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1272 = true := by
  have hs : count1272 q = (countLit q [-74]) + (countLit q [-75, -79]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -79])
  have hm := merge_right (literal (valuationOf q) (1270)) (literal (valuationOf q) (1272)) (countLit q [-74]) (countLit q [-75, -79]) (count1272 q) 1 (meaning1270 q) (meaning1272 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1272 = true := counterClause96 (baseVal q)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E118.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112118
