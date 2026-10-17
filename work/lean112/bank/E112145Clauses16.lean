import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1261 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1255)) (literal (valuationOf q) (1261)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 3 1 (meaning1252 q) (meaning1255 q) (meaning1261 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1255 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1255 = false ∨ valuation q 1261 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1256 = false ∨ valuationOf q 1262 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1256)) (literal (valuationOf q) (1262)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 3 2 (meaning1252 q) (meaning1256 q) (meaning1262 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1256 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1256 = false ∨ valuation q 1262 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1263 = true := by
  have hs : count1258 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1252)) (literal (valuationOf q) (1257)) (literal (valuationOf q) (1263)) (countLit q [-14, -16, -18]) (countLit q [-21, -23, -24]) (count1258 q) 3 3 (meaning1252 q) (meaning1257 q) (meaning1263 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1257 = false ∨ valuation q 1263 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1266 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1260)) (literal (valuationOf q) (1266)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 3 (meaning1260 q) (meaning1266 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1266 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1267 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1261)) (literal (valuationOf q) (1267)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 4 (meaning1261 q) (meaning1267 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1267 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1268 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1262)) (literal (valuationOf q) (1268)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 5 (meaning1262 q) (meaning1268 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1268 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1269 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1263)) (literal (valuationOf q) (1269)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 6 (meaning1263 q) (meaning1269 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1269 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1242)) (literal (valuationOf q) (1264)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 1 (meaning1242 q) (meaning1264 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1264 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1265 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1242)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1265)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 1 1 (meaning1242 q) (meaning1258 q) (meaning1265 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1258 = false ∨ valuation q 1265 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1266 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1242)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1266)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 1 2 (meaning1242 q) (meaning1259 q) (meaning1266 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1259 = false ∨ valuation q 1266 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1267 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1242)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1267)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 1 3 (meaning1242 q) (meaning1260 q) (meaning1267 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1260 = false ∨ valuation q 1267 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1268 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1242)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1268)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 1 4 (meaning1242 q) (meaning1261 q) (meaning1268 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1261 = false ∨ valuation q 1268 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1265 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1243)) (literal (valuationOf q) (1265)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 2 (meaning1243 q) (meaning1265 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1265 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1266 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1266)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 2 1 (meaning1243 q) (meaning1258 q) (meaning1266 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1258 = false ∨ valuation q 1266 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1267 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1267)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 2 2 (meaning1243 q) (meaning1259 q) (meaning1267 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1259 = false ∨ valuation q 1267 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1268 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1268)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 2 3 (meaning1243 q) (meaning1260 q) (meaning1268 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1260 = false ∨ valuation q 1268 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1269 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1269)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 2 4 (meaning1243 q) (meaning1261 q) (meaning1269 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1261 = false ∨ valuation q 1269 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1266 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1244)) (literal (valuationOf q) (1266)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 3 (meaning1244 q) (meaning1266 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1266 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1267 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1267)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 3 1 (meaning1244 q) (meaning1258 q) (meaning1267 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1258 = false ∨ valuation q 1267 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1268 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1268)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 3 2 (meaning1244 q) (meaning1259 q) (meaning1268 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1259 = false ∨ valuation q 1268 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1269 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1269)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 3 3 (meaning1244 q) (meaning1260 q) (meaning1269 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1260 = false ∨ valuation q 1269 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1270 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1270)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 3 4 (meaning1244 q) (meaning1261 q) (meaning1270 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1261 = false ∨ valuation q 1270 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1267 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1245)) (literal (valuationOf q) (1267)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 4 (meaning1245 q) (meaning1267 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1267 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1269 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1245)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1269)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 4 2 (meaning1245 q) (meaning1259 q) (meaning1269 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1259 = false ∨ valuation q 1269 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 1246 = false ∨ valuationOf q 1268 = true := by
  have hs : count1264 q = (countLit q [-2, -6, -7, -8, -11, -13]) + (countLit q [-14, -16, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13]) (l₂ := [-14, -16, -18, -21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1246)) (literal (valuationOf q) (1268)) (countLit q [-2, -6, -7, -8, -11, -13]) (countLit q [-14, -16, -18, -21, -23, -24]) (count1264 q) 5 (meaning1246 q) (meaning1268 q) hs
  change valuationOf q 1246 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 1246 = false ∨ valuation q 1268 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1275)) (countLit q [-29]) (countLit q [-30]) (count1275 q) 1 (meaningNeg30 q) (meaning1275 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1275 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1275)) (countLit q [-29]) (countLit q [-30]) (count1275 q) 1 (meaningNeg29 q) (meaning1275 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1275 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1276 = true := by
  have hs : count1275 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1276)) (countLit q [-29]) (countLit q [-30]) (count1275 q) 1 1 (meaningNeg29 q) (meaningNeg30 q) (meaning1276 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1276 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 1276 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-25]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1275)) (literal (valuationOf q) (1277)) (countLit q [-25]) (countLit q [-29, -30]) (count1277 q) 1 (meaning1275 q) (meaning1277 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1277 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1276 = false ∨ valuationOf q 1278 = true := by
  have hs : count1277 q = (countLit q [-25]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1276)) (literal (valuationOf q) (1278)) (countLit q [-25]) (countLit q [-29, -30]) (count1277 q) 2 (meaning1276 q) (meaning1278 q) hs
  change valuationOf q 1276 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1276 = false ∨ valuation q 1278 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-25]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-29, -30])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1277)) (countLit q [-25]) (countLit q [-29, -30]) (count1277 q) 1 (meaningNeg25 q) (meaning1277 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1277 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1275 = false ∨ valuationOf q 1278 = true := by
  have hs : count1277 q = (countLit q [-25]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (1275)) (literal (valuationOf q) (1278)) (countLit q [-25]) (countLit q [-29, -30]) (count1277 q) 1 1 (meaningNeg25 q) (meaning1275 q) (meaning1278 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1275 = false ∨ valuation q 1278 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E145.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112145
