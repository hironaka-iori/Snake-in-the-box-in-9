import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1275 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1269)) (literal (valuationOf q) (1275)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 3 (meaning1269 q) (meaning1275 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1275 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1274 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1274)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 1 1 (meaning1251 q) (meaning1267 q) (meaning1274 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1267 = false ∨ valuation q 1274 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1275 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1275)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 1 2 (meaning1251 q) (meaning1268 q) (meaning1275 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1268 = false ∨ valuation q 1275 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1276 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1269)) (literal (valuationOf q) (1276)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 1 3 (meaning1251 q) (meaning1269 q) (meaning1276 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1269 = false ∨ valuation q 1276 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1275 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1275)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 2 1 (meaning1252 q) (meaning1267 q) (meaning1275 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1267 = false ∨ valuation q 1275 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1276 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1276)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 2 2 (meaning1252 q) (meaning1268 q) (meaning1276 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1268 = false ∨ valuation q 1276 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1276 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1253)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1276)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 3 1 (meaning1253 q) (meaning1267 q) (meaning1276 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1267 = false ∨ valuation q 1276 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1277 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1277)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 4 1 (meaning1254 q) (meaning1267 q) (meaning1277 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1267 = false ∨ valuation q 1277 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1278 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1278)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 4 2 (meaning1254 q) (meaning1268 q) (meaning1278 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1268 = false ∨ valuation q 1278 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1278 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1255)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1278)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 5 1 (meaning1255 q) (meaning1267 q) (meaning1278 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1267 = false ∨ valuation q 1278 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1283)) (countLit q [-30]) (countLit q [-33]) (count1283 q) 1 (meaningNeg33 q) (meaning1283 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1283 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1283)) (countLit q [-30]) (countLit q [-33]) (count1283 q) 1 (meaningNeg30 q) (meaning1283 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1283 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1284 = true := by
  have hs : count1283 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1284)) (countLit q [-30]) (countLit q [-33]) (count1283 q) 1 1 (meaningNeg30 q) (meaningNeg33 q) (meaning1284 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 1284 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-27]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (1283)) (literal (valuationOf q) (1285)) (countLit q [-27]) (countLit q [-30, -33]) (count1285 q) 1 (meaning1283 q) (meaning1285 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1285 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1286 = true := by
  have hs : count1285 q = (countLit q [-27]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (1284)) (literal (valuationOf q) (1286)) (countLit q [-27]) (countLit q [-30, -33]) (count1285 q) 2 (meaning1284 q) (meaning1286 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1286 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-27]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -33])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1285)) (countLit q [-27]) (countLit q [-30, -33]) (count1285 q) 1 (meaningNeg27 q) (meaning1285 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1285 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1288)) (countLit q [-36]) (countLit q [-38]) (count1288 q) 1 (meaningNeg38 q) (meaning1288 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1288 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1288)) (countLit q [-36]) (countLit q [-38]) (count1288 q) 1 (meaningNeg36 q) (meaning1288 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1288 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1289)) (countLit q [-36]) (countLit q [-38]) (count1288 q) 1 1 (meaningNeg36 q) (meaningNeg38 q) (meaning1289 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 38 = true ∨ valuation q 1289 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-35]) + (countLit q [-36, -38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36, -38])
  have hm := merge_right (literal (valuationOf q) (1288)) (literal (valuationOf q) (1290)) (countLit q [-35]) (countLit q [-36, -38]) (count1290 q) 1 (meaning1288 q) (meaning1290 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1290 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1291 = true := by
  have hs : count1290 q = (countLit q [-35]) + (countLit q [-36, -38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36, -38])
  have hm := merge_right (literal (valuationOf q) (1289)) (literal (valuationOf q) (1291)) (countLit q [-35]) (countLit q [-36, -38]) (count1290 q) 2 (meaning1289 q) (meaning1291 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1291 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-35]) + (countLit q [-36, -38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36, -38])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1290)) (countLit q [-35]) (countLit q [-36, -38]) (count1290 q) 1 (meaningNeg35 q) (meaning1290 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1290 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1288 = false ∨ valuationOf q 1291 = true := by
  have hs : count1290 q = (countLit q [-35]) + (countLit q [-36, -38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36, -38])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1291)) (countLit q [-35]) (countLit q [-36, -38]) (count1290 q) 1 1 (meaningNeg35 q) (meaning1288 q) (meaning1291 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1288 = false ∨ valuation q 1291 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -36, -38])
  have hm := merge_right (literal (valuationOf q) (1290)) (literal (valuationOf q) (1293)) (countLit q [-27, -30, -33]) (countLit q [-35, -36, -38]) (count1293 q) 1 (meaning1290 q) (meaning1293 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1293 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -36, -38])
  have hm := merge_right (literal (valuationOf q) (1291)) (literal (valuationOf q) (1294)) (countLit q [-27, -30, -33]) (countLit q [-35, -36, -38]) (count1293 q) 2 (meaning1291 q) (meaning1294 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1294 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -36, -38])
  have hm := merge_left (literal (valuationOf q) (1285)) (literal (valuationOf q) (1293)) (countLit q [-27, -30, -33]) (countLit q [-35, -36, -38]) (count1293 q) 1 (meaning1285 q) (meaning1293 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1293 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -36, -38])
  have hm := merge_two (literal (valuationOf q) (1285)) (literal (valuationOf q) (1290)) (literal (valuationOf q) (1294)) (countLit q [-27, -30, -33]) (countLit q [-35, -36, -38]) (count1293 q) 1 1 (meaning1285 q) (meaning1290 q) (meaning1294 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1290 = false ∨ valuation q 1294 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -36, -38])
  have hm := merge_left (literal (valuationOf q) (1286)) (literal (valuationOf q) (1294)) (countLit q [-27, -30, -33]) (countLit q [-35, -36, -38]) (count1293 q) 2 (meaning1286 q) (meaning1294 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1294 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1299)) (countLit q [-43]) (countLit q [-44]) (count1299 q) 1 (meaningNeg44 q) (meaning1299 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1299 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1299)) (countLit q [-43]) (countLit q [-44]) (count1299 q) 1 (meaningNeg43 q) (meaning1299 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1299 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1300 = true := by
  have hs : count1299 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1300)) (countLit q [-43]) (countLit q [-44]) (count1299 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning1300 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 1300 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (1299)) (literal (valuationOf q) (1301)) (countLit q [-42]) (countLit q [-43, -44]) (count1301 q) 1 (meaning1299 q) (meaning1301 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1301 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E175.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112175
