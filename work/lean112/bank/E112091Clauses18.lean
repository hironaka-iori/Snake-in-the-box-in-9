import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1252 = false ∨ valuationOf q 1255 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1252)) (literal (valuationOf q) (1255)) (countLit q [-2]) (countLit q [-4, -7]) (count1254 q) 1 1 (meaningNeg2 q) (meaning1252 q) (meaning1255 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1252 = false ∨ valuation q 1255 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1253 = false ∨ valuationOf q 1256 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1253)) (literal (valuationOf q) (1256)) (countLit q [-2]) (countLit q [-4, -7]) (count1254 q) 1 2 (meaningNeg2 q) (meaning1253 q) (meaning1256 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1256 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1253 = false ∨ valuation q 1256 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1257)) (countLit q [-9]) (countLit q [-10]) (count1257 q) 1 (meaningNeg10 q) (meaning1257 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1257 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1257)) (countLit q [-9]) (countLit q [-10]) (count1257 q) 1 (meaningNeg9 q) (meaning1257 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1257 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1257 = false ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_right (literal (valuationOf q) (1257)) (literal (valuationOf q) (1259)) (countLit q [-8]) (countLit q [-9, -10]) (count1259 q) 1 (meaning1257 q) (meaning1259 q) hs
  change valuationOf q 1257 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1257 = false ∨ valuation q 1259 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1259)) (countLit q [-8]) (countLit q [-9, -10]) (count1259 q) 1 (meaningNeg8 q) (meaning1259 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1259 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1257)) (literal (valuationOf q) (1260)) (countLit q [-8]) (countLit q [-9, -10]) (count1259 q) 1 1 (meaningNeg8 q) (meaning1257 q) (meaning1260 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1257 = false ∨ valuation q 1260 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -9, -10])
  have hm := merge_right (literal (valuationOf q) (1259)) (literal (valuationOf q) (1262)) (countLit q [-2, -4, -7]) (countLit q [-8, -9, -10]) (count1262 q) 1 (meaning1259 q) (meaning1262 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1262 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -9, -10])
  have hm := merge_right (literal (valuationOf q) (1260)) (literal (valuationOf q) (1263)) (countLit q [-2, -4, -7]) (countLit q [-8, -9, -10]) (count1262 q) 2 (meaning1260 q) (meaning1263 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1263 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -9, -10])
  have hm := merge_left (literal (valuationOf q) (1254)) (literal (valuationOf q) (1262)) (countLit q [-2, -4, -7]) (countLit q [-8, -9, -10]) (count1262 q) 1 (meaning1254 q) (meaning1262 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1262 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1263)) (countLit q [-2, -4, -7]) (countLit q [-8, -9, -10]) (count1262 q) 1 1 (meaning1254 q) (meaning1259 q) (meaning1263 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1259 = false ∨ valuation q 1263 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1264)) (countLit q [-2, -4, -7]) (countLit q [-8, -9, -10]) (count1262 q) 1 2 (meaning1254 q) (meaning1260 q) (meaning1264 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1260 = false ∨ valuation q 1264 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -9, -10])
  have hm := merge_left (literal (valuationOf q) (1255)) (literal (valuationOf q) (1263)) (countLit q [-2, -4, -7]) (countLit q [-8, -9, -10]) (count1262 q) 2 (meaning1255 q) (meaning1263 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1263 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1255)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1264)) (countLit q [-2, -4, -7]) (countLit q [-8, -9, -10]) (count1262 q) 2 1 (meaning1255 q) (meaning1259 q) (meaning1264 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1259 = false ∨ valuation q 1264 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1256 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -9, -10])
  have hm := merge_left (literal (valuationOf q) (1256)) (literal (valuationOf q) (1264)) (countLit q [-2, -4, -7]) (countLit q [-8, -9, -10]) (count1262 q) 3 (meaning1256 q) (meaning1264 q) hs
  change valuationOf q 1256 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1256 = false ∨ valuation q 1264 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1268)) (countLit q [-14]) (countLit q [-15]) (count1268 q) 1 (meaningNeg15 q) (meaning1268 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1268 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1268)) (countLit q [-14]) (countLit q [-15]) (count1268 q) 1 (meaningNeg14 q) (meaning1268 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1268 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1269 = true := by
  have hs : count1268 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1269)) (countLit q [-14]) (countLit q [-15]) (count1268 q) 1 1 (meaningNeg14 q) (meaningNeg15 q) (meaning1269 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 15 = true ∨ valuation q 1269 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-11]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14, -15])
  have hm := merge_right (literal (valuationOf q) (1268)) (literal (valuationOf q) (1270)) (countLit q [-11]) (countLit q [-14, -15]) (count1270 q) 1 (meaning1268 q) (meaning1270 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1270 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1271 = true := by
  have hs : count1270 q = (countLit q [-11]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14, -15])
  have hm := merge_right (literal (valuationOf q) (1269)) (literal (valuationOf q) (1271)) (countLit q [-11]) (countLit q [-14, -15]) (count1270 q) 2 (meaning1269 q) (meaning1271 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1271 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-11]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14, -15])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1270)) (countLit q [-11]) (countLit q [-14, -15]) (count1270 q) 1 (meaningNeg11 q) (meaning1270 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1270 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1268 = false ∨ valuationOf q 1271 = true := by
  have hs : count1270 q = (countLit q [-11]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14, -15])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1271)) (countLit q [-11]) (countLit q [-14, -15]) (count1270 q) 1 1 (meaningNeg11 q) (meaning1268 q) (meaning1271 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1268 = false ∨ valuation q 1271 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1269 = false ∨ valuationOf q 1272 = true := by
  have hs : count1270 q = (countLit q [-11]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14, -15])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (1269)) (literal (valuationOf q) (1272)) (countLit q [-11]) (countLit q [-14, -15]) (count1270 q) 1 2 (meaningNeg11 q) (meaning1269 q) (meaning1272 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1269 = false ∨ valuation q 1272 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1273 = true := by
  have hs : count1273 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1273)) (countLit q [-18]) (countLit q [-20]) (count1273 q) 1 (meaningNeg20 q) (meaning1273 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1273 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1273 = true := by
  have hs : count1273 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1273)) (countLit q [-18]) (countLit q [-20]) (count1273 q) 1 (meaningNeg18 q) (meaning1273 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1273 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1274 = true := by
  have hs : count1273 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1274)) (countLit q [-18]) (countLit q [-20]) (count1273 q) 1 1 (meaningNeg18 q) (meaningNeg20 q) (meaning1274 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 1274 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-23]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1275)) (countLit q [-23]) (countLit q [-25]) (count1275 q) 1 (meaningNeg25 q) (meaning1275 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1275 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-23]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1275)) (countLit q [-23]) (countLit q [-25]) (count1275 q) 1 (meaningNeg23 q) (meaning1275 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1275 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-18, -20]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-23, -25])
  have hm := merge_right (literal (valuationOf q) (1275)) (literal (valuationOf q) (1277)) (countLit q [-18, -20]) (countLit q [-23, -25]) (count1277 q) 1 (meaning1275 q) (meaning1277 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1277 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-18, -20]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-23, -25])
  have hm := merge_left (literal (valuationOf q) (1273)) (literal (valuationOf q) (1277)) (countLit q [-18, -20]) (countLit q [-23, -25]) (count1277 q) 1 (meaning1273 q) (meaning1277 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1277 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1278 = true := by
  have hs : count1277 q = (countLit q [-18, -20]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-23, -25])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1275)) (literal (valuationOf q) (1278)) (countLit q [-18, -20]) (countLit q [-23, -25]) (count1277 q) 1 1 (meaning1273 q) (meaning1275 q) (meaning1278 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1275 = false ∨ valuation q 1278 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1279 = true := by
  have hs : count1277 q = (countLit q [-18, -20]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-23, -25])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1275)) (literal (valuationOf q) (1279)) (countLit q [-18, -20]) (countLit q [-23, -25]) (count1277 q) 2 1 (meaning1274 q) (meaning1275 q) (meaning1279 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1275 = false ∨ valuation q 1279 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E091.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112091
