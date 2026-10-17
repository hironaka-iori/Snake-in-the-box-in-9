import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-40, -41, -44]) + (countLit q [-45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -44]) (l₂ := [-45, -47, -49, -52])
  have hm := merge_right (literal (valuationOf q) (1284)) (literal (valuationOf q) (1288)) (countLit q [-40, -41, -44]) (countLit q [-45, -47, -49, -52]) (count1288 q) 1 (meaning1284 q) (meaning1288 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1288 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-40, -41, -44]) + (countLit q [-45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -44]) (l₂ := [-45, -47, -49, -52])
  have hm := merge_right (literal (valuationOf q) (1285)) (literal (valuationOf q) (1289)) (countLit q [-40, -41, -44]) (countLit q [-45, -47, -49, -52]) (count1288 q) 2 (meaning1285 q) (meaning1289 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1289 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-40, -41, -44]) + (countLit q [-45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -44]) (l₂ := [-45, -47, -49, -52])
  have hm := merge_right (literal (valuationOf q) (1286)) (literal (valuationOf q) (1290)) (countLit q [-40, -41, -44]) (countLit q [-45, -47, -49, -52]) (count1288 q) 3 (meaning1286 q) (meaning1290 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1290 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-40, -41, -44]) + (countLit q [-45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -44]) (l₂ := [-45, -47, -49, -52])
  have hm := merge_left (literal (valuationOf q) (1277)) (literal (valuationOf q) (1288)) (countLit q [-40, -41, -44]) (countLit q [-45, -47, -49, -52]) (count1288 q) 1 (meaning1277 q) (meaning1288 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1288 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-40, -41, -44]) + (countLit q [-45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -44]) (l₂ := [-45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1284)) (literal (valuationOf q) (1289)) (countLit q [-40, -41, -44]) (countLit q [-45, -47, -49, -52]) (count1288 q) 1 1 (meaning1277 q) (meaning1284 q) (meaning1289 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1284 = false ∨ valuation q 1289 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-40, -41, -44]) + (countLit q [-45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -44]) (l₂ := [-45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1285)) (literal (valuationOf q) (1290)) (countLit q [-40, -41, -44]) (countLit q [-45, -47, -49, -52]) (count1288 q) 1 2 (meaning1277 q) (meaning1285 q) (meaning1290 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1285 = false ∨ valuation q 1290 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1295 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_left (literal (valuationOf q) (1269)) (literal (valuationOf q) (1295)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 1 (meaning1269 q) (meaning1295 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1295 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1296 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1269)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1296)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 1 1 (meaning1269 q) (meaning1288 q) (meaning1296 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1288 = false ∨ valuation q 1296 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1297 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1269)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1297)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 1 2 (meaning1269 q) (meaning1289 q) (meaning1297 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1289 = false ∨ valuation q 1297 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1298 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1269)) (literal (valuationOf q) (1290)) (literal (valuationOf q) (1298)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 1 3 (meaning1269 q) (meaning1290 q) (meaning1298 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1290 = false ∨ valuation q 1298 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1296 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_left (literal (valuationOf q) (1270)) (literal (valuationOf q) (1296)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 2 (meaning1270 q) (meaning1296 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1296 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1297 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1297)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 2 1 (meaning1270 q) (meaning1288 q) (meaning1297 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1288 = false ∨ valuation q 1297 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1298 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1298)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 2 2 (meaning1270 q) (meaning1289 q) (meaning1298 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1289 = false ∨ valuation q 1298 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1299 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1290)) (literal (valuationOf q) (1299)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 2 3 (meaning1270 q) (meaning1290 q) (meaning1299 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1290 = false ∨ valuation q 1299 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1297 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_left (literal (valuationOf q) (1271)) (literal (valuationOf q) (1297)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 3 (meaning1271 q) (meaning1297 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1297 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1298 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1298)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 3 1 (meaning1271 q) (meaning1288 q) (meaning1298 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1288 = false ∨ valuation q 1298 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1299 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1299)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 3 2 (meaning1271 q) (meaning1289 q) (meaning1299 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1289 = false ∨ valuation q 1299 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1298 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_left (literal (valuationOf q) (1272)) (literal (valuationOf q) (1298)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 4 (meaning1272 q) (meaning1298 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1298 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1299 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1299)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 4 1 (meaning1272 q) (meaning1288 q) (meaning1299 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1288 = false ∨ valuation q 1299 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1300 = true := by
  have hs : count1295 q = (countLit q [-28, -29, -31, -33, -36, -38]) + (countLit q [-40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -36, -38]) (l₂ := [-40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1300)) (countLit q [-28, -29, -31, -33, -36, -38]) (countLit q [-40, -41, -44, -45, -47, -49, -52]) (count1295 q) 4 2 (meaning1272 q) (meaning1289 q) (meaning1300 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1289 = false ∨ valuation q 1300 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1310 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1247)) (literal (valuationOf q) (1295)) (literal (valuationOf q) (1310)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 2 1 (meaning1247 q) (meaning1295 q) (meaning1310 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1295 = false ∨ valuation q 1310 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1311 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1247)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1311)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 2 2 (meaning1247 q) (meaning1296 q) (meaning1311 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1296 = false ∨ valuation q 1311 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1312 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1247)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1312)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 2 3 (meaning1247 q) (meaning1297 q) (meaning1312 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1297 = false ∨ valuation q 1312 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1313 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1247)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1313)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 2 4 (meaning1247 q) (meaning1298 q) (meaning1313 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1298 = false ∨ valuation q 1313 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1314 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1247)) (literal (valuationOf q) (1299)) (literal (valuationOf q) (1314)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 2 5 (meaning1247 q) (meaning1299 q) (meaning1314 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1299 = false ∨ valuation q 1314 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1300 = false ∨ valuationOf q 1315 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1247)) (literal (valuationOf q) (1300)) (literal (valuationOf q) (1315)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 2 6 (meaning1247 q) (meaning1300 q) (meaning1315 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1300 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1300 = false ∨ valuation q 1315 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1311 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1248)) (literal (valuationOf q) (1295)) (literal (valuationOf q) (1311)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 3 1 (meaning1248 q) (meaning1295 q) (meaning1311 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1295 = false ∨ valuation q 1311 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1312 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1248)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1312)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 3 2 (meaning1248 q) (meaning1296 q) (meaning1312 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1296 = false ∨ valuation q 1312 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1313 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1248)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1313)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 3 3 (meaning1248 q) (meaning1297 q) (meaning1313 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1297 = false ∨ valuation q 1313 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1314 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1248)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1314)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 3 4 (meaning1248 q) (meaning1298 q) (meaning1314 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1298 = false ∨ valuation q 1314 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1315 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1248)) (literal (valuationOf q) (1299)) (literal (valuationOf q) (1315)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 3 5 (meaning1248 q) (meaning1299 q) (meaning1315 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1299 = false ∨ valuation q 1315 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1312 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1295)) (literal (valuationOf q) (1312)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 4 1 (meaning1249 q) (meaning1295 q) (meaning1312 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1295 = false ∨ valuation q 1312 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E094.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112094
