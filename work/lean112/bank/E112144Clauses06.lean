import E112144Semantics
import B112E144Inputs
namespace Snake9.Regrowth.E112144
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (1255)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1264)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 2 1 (meaning1255 q) (meaning1259 q) (meaning1264 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1259 = false ∨ valuation q 1264 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1265 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (1255)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1265)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 2 2 (meaning1255 q) (meaning1260 q) (meaning1265 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1260 = false ∨ valuation q 1265 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 1256 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_left (literal (valuationOf q) (1256)) (literal (valuationOf q) (1264)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 3 (meaning1256 q) (meaning1264 q) hs
  change valuationOf q 1256 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 1256 = false ∨ valuation q 1264 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 1256 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1265 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (1256)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1265)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 3 1 (meaning1256 q) (meaning1259 q) (meaning1265 q) hs
  change valuationOf q 1256 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 1256 = false ∨ valuation q 1259 = false ∨ valuation q 1265 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1268)) (countLit q [-14]) (countLit q [-17]) (count1268 q) 1 (meaningNeg17 q) (meaning1268 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1268 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1268)) (countLit q [-14]) (countLit q [-17]) (count1268 q) 1 (meaningNeg14 q) (meaning1268 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1268 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -17])
  have hm := merge_right (literal (valuationOf q) (1268)) (literal (valuationOf q) (1270)) (countLit q [-12]) (countLit q [-14, -17]) (count1270 q) 1 (meaning1268 q) (meaning1270 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1270 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -17])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1270)) (countLit q [-12]) (countLit q [-14, -17]) (count1270 q) 1 (meaningNeg12 q) (meaning1270 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1270 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1268 = false ∨ valuationOf q 1271 = true := by
  have hs : count1270 q = (countLit q [-12]) + (countLit q [-14, -17]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -17])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1271)) (countLit q [-12]) (countLit q [-14, -17]) (count1270 q) 1 1 (meaningNeg12 q) (meaning1268 q) (meaning1271 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1268 = false ∨ valuation q 1271 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1273 = true := by
  have hs : count1273 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1273)) (countLit q [-19]) (countLit q [-20]) (count1273 q) 1 (meaningNeg19 q) (meaning1273 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1273 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1274 = true := by
  have hs : count1273 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1274)) (countLit q [-19]) (countLit q [-20]) (count1273 q) 1 1 (meaningNeg19 q) (meaningNeg20 q) (meaning1274 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 1274 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-23]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1275)) (countLit q [-23]) (countLit q [-26]) (count1275 q) 1 (meaningNeg23 q) (meaning1275 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1275 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-19, -20]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -26])
  have hm := merge_right (literal (valuationOf q) (1275)) (literal (valuationOf q) (1277)) (countLit q [-19, -20]) (countLit q [-23, -26]) (count1277 q) 1 (meaning1275 q) (meaning1277 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1277 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-19, -20]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -26])
  have hm := merge_left (literal (valuationOf q) (1273)) (literal (valuationOf q) (1277)) (countLit q [-19, -20]) (countLit q [-23, -26]) (count1277 q) 1 (meaning1273 q) (meaning1277 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1277 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1278 = true := by
  have hs : count1277 q = (countLit q [-19, -20]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -26])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1275)) (literal (valuationOf q) (1278)) (countLit q [-19, -20]) (countLit q [-23, -26]) (count1277 q) 1 1 (meaning1273 q) (meaning1275 q) (meaning1278 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1275 = false ∨ valuation q 1278 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1278 = true := by
  have hs : count1277 q = (countLit q [-19, -20]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -26])
  have hm := merge_left (literal (valuationOf q) (1274)) (literal (valuationOf q) (1278)) (countLit q [-19, -20]) (countLit q [-23, -26]) (count1277 q) 2 (meaning1274 q) (meaning1278 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1278 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1281 = true := by
  have hs : count1281 q = (countLit q [-12, -14, -17]) + (countLit q [-19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -17]) (l₂ := [-19, -20, -23, -26])
  have hm := merge_right (literal (valuationOf q) (1277)) (literal (valuationOf q) (1281)) (countLit q [-12, -14, -17]) (countLit q [-19, -20, -23, -26]) (count1281 q) 1 (meaning1277 q) (meaning1281 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1281 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1282 = true := by
  have hs : count1281 q = (countLit q [-12, -14, -17]) + (countLit q [-19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -17]) (l₂ := [-19, -20, -23, -26])
  have hm := merge_right (literal (valuationOf q) (1278)) (literal (valuationOf q) (1282)) (countLit q [-12, -14, -17]) (countLit q [-19, -20, -23, -26]) (count1281 q) 2 (meaning1278 q) (meaning1282 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1282 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1281 = true := by
  have hs : count1281 q = (countLit q [-12, -14, -17]) + (countLit q [-19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -17]) (l₂ := [-19, -20, -23, -26])
  have hm := merge_left (literal (valuationOf q) (1270)) (literal (valuationOf q) (1281)) (countLit q [-12, -14, -17]) (countLit q [-19, -20, -23, -26]) (count1281 q) 1 (meaning1270 q) (meaning1281 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1281 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1282 = true := by
  have hs : count1281 q = (countLit q [-12, -14, -17]) + (countLit q [-19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -17]) (l₂ := [-19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1277)) (literal (valuationOf q) (1282)) (countLit q [-12, -14, -17]) (countLit q [-19, -20, -23, -26]) (count1281 q) 1 1 (meaning1270 q) (meaning1277 q) (meaning1282 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1277 = false ∨ valuation q 1282 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1283 = true := by
  have hs : count1281 q = (countLit q [-12, -14, -17]) + (countLit q [-19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -17]) (l₂ := [-19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1278)) (literal (valuationOf q) (1283)) (countLit q [-12, -14, -17]) (countLit q [-19, -20, -23, -26]) (count1281 q) 1 2 (meaning1270 q) (meaning1278 q) (meaning1283 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1278 = false ∨ valuation q 1283 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1282 = true := by
  have hs : count1281 q = (countLit q [-12, -14, -17]) + (countLit q [-19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -17]) (l₂ := [-19, -20, -23, -26])
  have hm := merge_left (literal (valuationOf q) (1271)) (literal (valuationOf q) (1282)) (countLit q [-12, -14, -17]) (countLit q [-19, -20, -23, -26]) (count1281 q) 2 (meaning1271 q) (meaning1282 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1282 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1283 = true := by
  have hs : count1281 q = (countLit q [-12, -14, -17]) + (countLit q [-19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -17]) (l₂ := [-19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1277)) (literal (valuationOf q) (1283)) (countLit q [-12, -14, -17]) (countLit q [-19, -20, -23, -26]) (count1281 q) 2 1 (meaning1271 q) (meaning1277 q) (meaning1283 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1277 = false ∨ valuation q 1283 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1284 = true := by
  have hs : count1281 q = (countLit q [-12, -14, -17]) + (countLit q [-19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -17]) (l₂ := [-19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1278)) (literal (valuationOf q) (1284)) (countLit q [-12, -14, -17]) (countLit q [-19, -20, -23, -26]) (count1281 q) 2 2 (meaning1271 q) (meaning1278 q) (meaning1284 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1278 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1278 = false ∨ valuation q 1284 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 1282 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_right (literal (valuationOf q) (1282)) (literal (valuationOf q) (1289)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 2 (meaning1282 q) (meaning1289 q) hs
  change valuationOf q 1282 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 1282 = false ∨ valuation q 1289 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1289)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 1 1 (meaning1262 q) (meaning1281 q) (meaning1289 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1281 = false ∨ valuation q 1289 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1290)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 1 2 (meaning1262 q) (meaning1282 q) (meaning1290 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1282 = false ∨ valuation q 1290 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1291)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 1 3 (meaning1262 q) (meaning1283 q) (meaning1291 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1283 = false ∨ valuation q 1291 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_left (literal (valuationOf q) (1263)) (literal (valuationOf q) (1289)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 2 (meaning1263 q) (meaning1289 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1289 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1290)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 2 1 (meaning1263 q) (meaning1281 q) (meaning1290 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1281 = false ∨ valuation q 1290 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1291)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 2 2 (meaning1263 q) (meaning1282 q) (meaning1291 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1282 = false ∨ valuation q 1291 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1292 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1292)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 2 3 (meaning1263 q) (meaning1283 q) (meaning1292 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1283 = false ∨ valuation q 1292 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E144.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112144
