import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1253)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 2 1 (meaning1244 q) (meaning1248 q) (meaning1253 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1248 = false ∨ valuation q 1253 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1254 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1254)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 2 2 (meaning1244 q) (meaning1249 q) (meaning1254 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1249 = false ∨ valuation q 1254 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1250 = false ∨ valuationOf q 1255 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1250)) (literal (valuationOf q) (1255)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 2 3 (meaning1244 q) (meaning1250 q) (meaning1255 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1250 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1250 = false ∨ valuation q 1255 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1254 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1245)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1254)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 3 1 (meaning1245 q) (meaning1248 q) (meaning1254 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1248 = false ∨ valuation q 1254 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1255 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1245)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1255)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 3 2 (meaning1245 q) (meaning1249 q) (meaning1255 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1249 = false ∨ valuation q 1255 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1257)) (countLit q [-18]) (countLit q [-21]) (count1257 q) 1 (meaningNeg21 q) (meaning1257 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1257 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1257)) (countLit q [-18]) (countLit q [-21]) (count1257 q) 1 (meaningNeg18 q) (meaning1257 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1257 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1258 = true := by
  have hs : count1257 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1258)) (countLit q [-18]) (countLit q [-21]) (count1257 q) 1 1 (meaningNeg18 q) (meaningNeg21 q) (meaning1258 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 21 = true ∨ valuation q 1258 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 1257 = false ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_right (literal (valuationOf q) (1257)) (literal (valuationOf q) (1259)) (countLit q [-15]) (countLit q [-18, -21]) (count1259 q) 1 (meaning1257 q) (meaning1259 q) hs
  change valuationOf q 1257 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 1257 = false ∨ valuation q 1259 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1258 = false ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_right (literal (valuationOf q) (1258)) (literal (valuationOf q) (1260)) (countLit q [-15]) (countLit q [-18, -21]) (count1259 q) 2 (meaning1258 q) (meaning1260 q) hs
  change valuationOf q 1258 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1258 = false ∨ valuation q 1260 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1259)) (countLit q [-15]) (countLit q [-18, -21]) (count1259 q) 1 (meaningNeg15 q) (meaning1259 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1259 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (1257)) (literal (valuationOf q) (1260)) (countLit q [-15]) (countLit q [-18, -21]) (count1259 q) 1 1 (meaningNeg15 q) (meaning1257 q) (meaning1260 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1257 = false ∨ valuation q 1260 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1258 = false ∨ valuationOf q 1261 = true := by
  have hs : count1259 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1261)) (countLit q [-15]) (countLit q [-18, -21]) (count1259 q) 1 2 (meaningNeg15 q) (meaning1258 q) (meaning1261 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1258 = false ∨ valuation q 1261 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-23]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1262)) (countLit q [-23]) (countLit q [-25]) (count1262 q) 1 (meaningNeg25 q) (meaning1262 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1262 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-23]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1262)) (countLit q [-23]) (countLit q [-25]) (count1262 q) 1 (meaningNeg23 q) (meaning1262 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1262 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-23]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1263)) (countLit q [-23]) (countLit q [-25]) (count1262 q) 1 1 (meaningNeg23 q) (meaningNeg25 q) (meaning1263 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 25 = true ∨ valuation q 1263 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-22]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23, -25])
  have hm := merge_right (literal (valuationOf q) (1262)) (literal (valuationOf q) (1264)) (countLit q [-22]) (countLit q [-23, -25]) (count1264 q) 1 (meaning1262 q) (meaning1264 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1264 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1265 = true := by
  have hs : count1264 q = (countLit q [-22]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23, -25])
  have hm := merge_right (literal (valuationOf q) (1263)) (literal (valuationOf q) (1265)) (countLit q [-22]) (countLit q [-23, -25]) (count1264 q) 2 (meaning1263 q) (meaning1265 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1265 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-22]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23, -25])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1264)) (countLit q [-22]) (countLit q [-23, -25]) (count1264 q) 1 (meaningNeg22 q) (meaning1264 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1264 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1262 = false ∨ valuationOf q 1265 = true := by
  have hs : count1264 q = (countLit q [-22]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23, -25])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (1262)) (literal (valuationOf q) (1265)) (countLit q [-22]) (countLit q [-23, -25]) (count1264 q) 1 1 (meaningNeg22 q) (meaning1262 q) (meaning1265 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1262 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1262 = false ∨ valuation q 1265 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1263 = false ∨ valuationOf q 1266 = true := by
  have hs : count1264 q = (countLit q [-22]) + (countLit q [-23, -25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23, -25])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (1263)) (literal (valuationOf q) (1266)) (countLit q [-22]) (countLit q [-23, -25]) (count1264 q) 1 2 (meaningNeg22 q) (meaning1263 q) (meaning1266 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1263 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1263 = false ∨ valuation q 1266 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1267 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1264)) (literal (valuationOf q) (1267)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 1 (meaning1264 q) (meaning1267 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1267 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1268 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1265)) (literal (valuationOf q) (1268)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 2 (meaning1265 q) (meaning1268 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1268 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1269 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1266)) (literal (valuationOf q) (1269)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 3 (meaning1266 q) (meaning1269 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1269 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1267 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_left (literal (valuationOf q) (1259)) (literal (valuationOf q) (1267)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 1 (meaning1259 q) (meaning1267 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1267 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1268 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1259)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1268)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 1 1 (meaning1259 q) (meaning1264 q) (meaning1268 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1264 = false ∨ valuation q 1268 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1265 = false ∨ valuationOf q 1269 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1259)) (literal (valuationOf q) (1265)) (literal (valuationOf q) (1269)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 1 2 (meaning1259 q) (meaning1265 q) (meaning1269 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1265 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1265 = false ∨ valuation q 1269 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1268 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_left (literal (valuationOf q) (1260)) (literal (valuationOf q) (1268)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 2 (meaning1260 q) (meaning1268 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1268 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1269 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_two (literal (valuationOf q) (1260)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1269)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 2 1 (meaning1260 q) (meaning1264 q) (meaning1269 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1264 = false ∨ valuation q 1269 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1269 = true := by
  have hs : count1267 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25])
  have hm := merge_left (literal (valuationOf q) (1261)) (literal (valuationOf q) (1269)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25]) (count1267 q) 3 (meaning1261 q) (meaning1269 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1269 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1273 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1267)) (literal (valuationOf q) (1273)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 1 (meaning1267 q) (meaning1273 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1273 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1274 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-15, -18, -21, -22, -23, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-15, -18, -21, -22, -23, -25])
  have hm := merge_right (literal (valuationOf q) (1268)) (literal (valuationOf q) (1274)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-15, -18, -21, -22, -23, -25]) (count1273 q) 2 (meaning1268 q) (meaning1274 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1274 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E175.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112175
