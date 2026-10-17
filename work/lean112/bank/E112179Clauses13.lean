import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1258 = true := by
  have hs : count1257 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1258)) (countLit q [-17]) (countLit q [-20]) (count1257 q) 1 1 (meaningNeg17 q) (meaningNeg20 q) (meaning1258 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 20 = true ∨ valuation q 1258 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 1257 = false ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-14]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17, -20])
  have hm := merge_right (literal (valuationOf q) (1257)) (literal (valuationOf q) (1259)) (countLit q [-14]) (countLit q [-17, -20]) (count1259 q) 1 (meaning1257 q) (meaning1259 q) hs
  change valuationOf q 1257 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 1257 = false ∨ valuation q 1259 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1258 = false ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-14]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17, -20])
  have hm := merge_right (literal (valuationOf q) (1258)) (literal (valuationOf q) (1260)) (countLit q [-14]) (countLit q [-17, -20]) (count1259 q) 2 (meaning1258 q) (meaning1260 q) hs
  change valuationOf q 1258 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1258 = false ∨ valuation q 1260 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-14]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17, -20])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1259)) (countLit q [-14]) (countLit q [-17, -20]) (count1259 q) 1 (meaningNeg14 q) (meaning1259 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1259 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-14]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17, -20])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1257)) (literal (valuationOf q) (1260)) (countLit q [-14]) (countLit q [-17, -20]) (count1259 q) 1 1 (meaningNeg14 q) (meaning1257 q) (meaning1260 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1257 = false ∨ valuation q 1260 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1258 = false ∨ valuationOf q 1261 = true := by
  have hs : count1259 q = (countLit q [-14]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17, -20])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1261)) (countLit q [-14]) (countLit q [-17, -20]) (count1259 q) 1 2 (meaningNeg14 q) (meaning1258 q) (meaning1261 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1258 = false ∨ valuation q 1261 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1262)) (countLit q [-22]) (countLit q [-24]) (count1262 q) 1 (meaningNeg24 q) (meaning1262 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1262 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1262)) (countLit q [-22]) (countLit q [-24]) (count1262 q) 1 (meaningNeg22 q) (meaning1262 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1262 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1263)) (countLit q [-22]) (countLit q [-24]) (count1262 q) 1 1 (meaningNeg22 q) (meaningNeg24 q) (meaning1263 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 24 = true ∨ valuation q 1263 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-21]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -24])
  have hm := merge_right (literal (valuationOf q) (1262)) (literal (valuationOf q) (1264)) (countLit q [-21]) (countLit q [-22, -24]) (count1264 q) 1 (meaning1262 q) (meaning1264 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1264 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1265 = true := by
  have hs : count1264 q = (countLit q [-21]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -24])
  have hm := merge_right (literal (valuationOf q) (1263)) (literal (valuationOf q) (1265)) (countLit q [-21]) (countLit q [-22, -24]) (count1264 q) 2 (meaning1263 q) (meaning1265 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1265 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-21]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -24])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1264)) (countLit q [-21]) (countLit q [-22, -24]) (count1264 q) 1 (meaningNeg21 q) (meaning1264 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1264 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1267 = true := by
  have hs : count1267 q = (countLit q [-14, -17, -20]) + (countLit q [-21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -20]) (l₂ := [-21, -22, -24])
  have hm := merge_right (literal (valuationOf q) (1264)) (literal (valuationOf q) (1267)) (countLit q [-14, -17, -20]) (countLit q [-21, -22, -24]) (count1267 q) 1 (meaning1264 q) (meaning1267 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1267 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1268 = true := by
  have hs : count1267 q = (countLit q [-14, -17, -20]) + (countLit q [-21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -20]) (l₂ := [-21, -22, -24])
  have hm := merge_right (literal (valuationOf q) (1265)) (literal (valuationOf q) (1268)) (countLit q [-14, -17, -20]) (countLit q [-21, -22, -24]) (count1267 q) 2 (meaning1265 q) (meaning1268 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1268 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1267 = true := by
  have hs : count1267 q = (countLit q [-14, -17, -20]) + (countLit q [-21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -20]) (l₂ := [-21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1259)) (literal (valuationOf q) (1267)) (countLit q [-14, -17, -20]) (countLit q [-21, -22, -24]) (count1267 q) 1 (meaning1259 q) (meaning1267 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1267 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1268 = true := by
  have hs : count1267 q = (countLit q [-14, -17, -20]) + (countLit q [-21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -20]) (l₂ := [-21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1259)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1268)) (countLit q [-14, -17, -20]) (countLit q [-21, -22, -24]) (count1267 q) 1 1 (meaning1259 q) (meaning1264 q) (meaning1268 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1264 = false ∨ valuation q 1268 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1268 = true := by
  have hs : count1267 q = (countLit q [-14, -17, -20]) + (countLit q [-21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -20]) (l₂ := [-21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1260)) (literal (valuationOf q) (1268)) (countLit q [-14, -17, -20]) (countLit q [-21, -22, -24]) (count1267 q) 2 (meaning1260 q) (meaning1268 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1268 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1269 = true := by
  have hs : count1267 q = (countLit q [-14, -17, -20]) + (countLit q [-21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -20]) (l₂ := [-21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1260)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1269)) (countLit q [-14, -17, -20]) (countLit q [-21, -22, -24]) (count1267 q) 2 1 (meaning1260 q) (meaning1264 q) (meaning1269 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1264 = false ∨ valuation q 1269 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1269 = true := by
  have hs : count1267 q = (countLit q [-14, -17, -20]) + (countLit q [-21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -20]) (l₂ := [-21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1261)) (literal (valuationOf q) (1269)) (countLit q [-14, -17, -20]) (countLit q [-21, -22, -24]) (count1267 q) 3 (meaning1261 q) (meaning1269 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1269 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1273 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_right (literal (valuationOf q) (1267)) (literal (valuationOf q) (1273)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 1 (meaning1267 q) (meaning1273 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1273 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1274 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_right (literal (valuationOf q) (1268)) (literal (valuationOf q) (1274)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 2 (meaning1268 q) (meaning1274 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1274 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1275 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_right (literal (valuationOf q) (1269)) (literal (valuationOf q) (1275)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 3 (meaning1269 q) (meaning1275 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1275 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1274 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1274)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 1 1 (meaning1251 q) (meaning1267 q) (meaning1274 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1267 = false ∨ valuation q 1274 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1275 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1275)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 1 2 (meaning1251 q) (meaning1268 q) (meaning1275 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1268 = false ∨ valuation q 1275 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1276 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1269)) (literal (valuationOf q) (1276)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 1 3 (meaning1251 q) (meaning1269 q) (meaning1276 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1269 = false ∨ valuation q 1276 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1275 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1275)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 2 1 (meaning1252 q) (meaning1267 q) (meaning1275 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1267 = false ∨ valuation q 1275 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1276 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1276)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 2 2 (meaning1252 q) (meaning1268 q) (meaning1276 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1268 = false ∨ valuation q 1276 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1276 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1253)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1276)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 3 1 (meaning1253 q) (meaning1267 q) (meaning1276 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1267 = false ∨ valuation q 1276 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1277 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1253)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1277)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 3 2 (meaning1253 q) (meaning1268 q) (meaning1277 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1268 = false ∨ valuation q 1277 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1277 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1277)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 4 1 (meaning1254 q) (meaning1267 q) (meaning1277 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1267 = false ∨ valuation q 1277 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1278 = true := by
  have hs : count1273 q = (countLit q [-2, -6, -7, -8, -10, -12]) + (countLit q [-14, -17, -20, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12]) (l₂ := [-14, -17, -20, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1278)) (countLit q [-2, -6, -7, -8, -10, -12]) (countLit q [-14, -17, -20, -21, -22, -24]) (count1273 q) 4 2 (meaning1254 q) (meaning1268 q) (meaning1278 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1268 = false ∨ valuation q 1278 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-29]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (1283)) (countLit q [-29]) (countLit q [-32]) (count1283 q) 1 (meaningNeg32 q) (meaning1283 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1283 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E179.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112179
