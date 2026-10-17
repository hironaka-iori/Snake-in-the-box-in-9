import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1255 = true := by
  have hs : count1251 q = (countLit q [-39, -41, -44]) + (countLit q [-45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -44]) (l₂ := [-45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1241)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1255)) (countLit q [-39, -41, -44]) (countLit q [-45, -46, -47, -50]) (count1251 q) 2 3 (meaning1241 q) (meaning1249 q) (meaning1255 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1249 = false ∨ valuation q 1255 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1260 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1253)) (literal (valuationOf q) (1260)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 3 (meaning1253 q) (meaning1260 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1260 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 1232 = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1260 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1232)) (literal (valuationOf q) (1252)) (literal (valuationOf q) (1260)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 1 2 (meaning1232 q) (meaning1252 q) (meaning1260 q) hs
  change valuationOf q 1232 = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 1232 = false ∨ valuation q 1252 = false ∨ valuation q 1260 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 1232 = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1261 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1232)) (literal (valuationOf q) (1253)) (literal (valuationOf q) (1261)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 1 3 (meaning1232 q) (meaning1253 q) (meaning1261 q) hs
  change valuationOf q 1232 = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 1232 = false ∨ valuation q 1253 = false ∨ valuation q 1261 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 1232 = false ∨ valuationOf q 1254 = false ∨ valuationOf q 1262 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1232)) (literal (valuationOf q) (1254)) (literal (valuationOf q) (1262)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 1 4 (meaning1232 q) (meaning1254 q) (meaning1262 q) hs
  change valuationOf q 1232 = false ∨ valuationOf q 1254 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 1232 = false ∨ valuation q 1254 = false ∨ valuation q 1262 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1251 = false ∨ valuationOf q 1260 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1233)) (literal (valuationOf q) (1251)) (literal (valuationOf q) (1260)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 2 1 (meaning1233 q) (meaning1251 q) (meaning1260 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1251 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1251 = false ∨ valuation q 1260 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1261 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1233)) (literal (valuationOf q) (1252)) (literal (valuationOf q) (1261)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 2 2 (meaning1233 q) (meaning1252 q) (meaning1261 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1252 = false ∨ valuation q 1261 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1262 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1233)) (literal (valuationOf q) (1253)) (literal (valuationOf q) (1262)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 2 3 (meaning1233 q) (meaning1253 q) (meaning1262 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1253 = false ∨ valuation q 1262 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1254 = false ∨ valuationOf q 1263 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1233)) (literal (valuationOf q) (1254)) (literal (valuationOf q) (1263)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 2 4 (meaning1233 q) (meaning1254 q) (meaning1263 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1254 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1254 = false ∨ valuation q 1263 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1264 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1233)) (literal (valuationOf q) (1255)) (literal (valuationOf q) (1264)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 2 5 (meaning1233 q) (meaning1255 q) (meaning1264 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1255 = false ∨ valuation q 1264 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1251 = false ∨ valuationOf q 1261 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1234)) (literal (valuationOf q) (1251)) (literal (valuationOf q) (1261)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 3 1 (meaning1234 q) (meaning1251 q) (meaning1261 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1251 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1251 = false ∨ valuation q 1261 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1262 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1234)) (literal (valuationOf q) (1252)) (literal (valuationOf q) (1262)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 3 2 (meaning1234 q) (meaning1252 q) (meaning1262 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1252 = false ∨ valuation q 1262 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1263 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1234)) (literal (valuationOf q) (1253)) (literal (valuationOf q) (1263)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 3 3 (meaning1234 q) (meaning1253 q) (meaning1263 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1253 = false ∨ valuation q 1263 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1263 = true := by
  have hs : count1258 q = (countLit q [-28, -30, -32, -33, -35, -38]) + (countLit q [-39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -35, -38]) (l₂ := [-39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1235)) (literal (valuationOf q) (1252)) (literal (valuationOf q) (1263)) (countLit q [-28, -30, -32, -33, -35, -38]) (countLit q [-39, -41, -44, -45, -46, -47, -50]) (count1258 q) 4 2 (meaning1235 q) (meaning1252 q) (meaning1263 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1252 = false ∨ valuation q 1263 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1271 = true := by
  have hs : count1268 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) + (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (l₂ := [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1271)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (count1268 q) 1 3 (meaning1212 q) (meaning1260 q) (meaning1271 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1260 = false ∨ valuation q 1271 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1272 = true := by
  have hs : count1268 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) + (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (l₂ := [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1272)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (count1268 q) 1 4 (meaning1212 q) (meaning1261 q) (meaning1272 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1261 = false ∨ valuation q 1272 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1273 = true := by
  have hs : count1268 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) + (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (l₂ := [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1262)) (literal (valuationOf q) (1273)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (count1268 q) 1 5 (meaning1212 q) (meaning1262 q) (meaning1273 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1262 = false ∨ valuation q 1273 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1263 = false ∨ valuationOf q 1274 = true := by
  have hs : count1268 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) + (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (l₂ := [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1263)) (literal (valuationOf q) (1274)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (count1268 q) 1 6 (meaning1212 q) (meaning1263 q) (meaning1274 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1263 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1263 = false ∨ valuation q 1274 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1275 = true := by
  have hs : count1268 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) + (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (l₂ := [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1275)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (count1268 q) 1 7 (meaning1212 q) (meaning1264 q) (meaning1275 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1264 = false ∨ valuation q 1275 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1273 = true := by
  have hs : count1268 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) + (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (l₂ := [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1213)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1273)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (count1268 q) 2 4 (meaning1213 q) (meaning1261 q) (meaning1273 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1261 = false ∨ valuation q 1273 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1274 = true := by
  have hs : count1268 q = (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) + (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (l₂ := [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1213)) (literal (valuationOf q) (1262)) (literal (valuationOf q) (1274)) (countLit q [-2, -5, -6, -8, -11, -13, -16, -18, -19, -20, -23, -26]) (countLit q [-28, -30, -32, -33, -35, -38, -39, -41, -44, -45, -46, -47, -50]) (count1268 q) 2 5 (meaning1213 q) (meaning1262 q) (meaning1274 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1262 = false ∨ valuation q 1274 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1278 = true := by
  have hs : count1278 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1278)) (countLit q [-54]) (countLit q [-56]) (count1278 q) 1 (meaningNeg54 q) (meaning1278 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1278 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1279 = true := by
  have hs : count1278 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1279)) (countLit q [-54]) (countLit q [-56]) (count1278 q) 1 1 (meaningNeg54 q) (meaningNeg56 q) (meaning1279 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1279 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 1279 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (1278)) (literal (valuationOf q) (1280)) (countLit q [-53]) (countLit q [-54, -56]) (count1280 q) 1 (meaning1278 q) (meaning1280 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1280 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1279 = false ∨ valuationOf q 1281 = true := by
  have hs : count1280 q = (countLit q [-53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (1279)) (literal (valuationOf q) (1281)) (countLit q [-53]) (countLit q [-54, -56]) (count1280 q) 2 (meaning1279 q) (meaning1281 q) hs
  change valuationOf q 1279 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1279 = false ∨ valuation q 1281 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1278 = false ∨ valuationOf q 1281 = true := by
  have hs : count1280 q = (countLit q [-53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (1278)) (literal (valuationOf q) (1281)) (countLit q [-53]) (countLit q [-54, -56]) (count1280 q) 1 1 (meaningNeg53 q) (meaning1278 q) (meaning1281 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1278 = false ∨ valuation q 1281 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1283)) (countLit q [-60]) (countLit q [-62]) (count1283 q) 1 (meaningNeg60 q) (meaning1283 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1283 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-59]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -62])
  have hm := merge_right (literal (valuationOf q) (1283)) (literal (valuationOf q) (1285)) (countLit q [-59]) (countLit q [-60, -62]) (count1285 q) 1 (meaning1283 q) (meaning1285 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1285 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-59]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -62])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1285)) (countLit q [-59]) (countLit q [-60, -62]) (count1285 q) 1 (meaningNeg59 q) (meaning1285 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1285 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true := by
  have hs : count1285 q = (countLit q [-59]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -62])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1286)) (countLit q [-59]) (countLit q [-60, -62]) (count1285 q) 1 1 (meaningNeg59 q) (meaning1283 q) (meaning1286 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1283 = false ∨ valuation q 1286 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-53, -54, -56]) + (countLit q [-59, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56]) (l₂ := [-59, -60, -62])
  have hm := merge_left (literal (valuationOf q) (1280)) (literal (valuationOf q) (1288)) (countLit q [-53, -54, -56]) (countLit q [-59, -60, -62]) (count1288 q) 1 (meaning1280 q) (meaning1288 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1288 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-53, -54, -56]) + (countLit q [-59, -60, -62]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -56]) (l₂ := [-59, -60, -62])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1285)) (literal (valuationOf q) (1289)) (countLit q [-53, -54, -56]) (countLit q [-59, -60, -62]) (count1288 q) 1 1 (meaning1280 q) (meaning1285 q) (meaning1289 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1285 = false ∨ valuation q 1289 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E154.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112154
