import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1259 = false ∨ valuationOf q 1262 = true := by
  have hs : count1261 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1262)) (countLit q [-28]) (countLit q [-29, -31]) (count1261 q) 1 1 (meaningNeg28 q) (meaning1259 q) (meaning1262 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1259 = false ∨ valuation q 1262 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1260 = false ∨ valuationOf q 1263 = true := by
  have hs : count1261 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1263)) (countLit q [-28]) (countLit q [-29, -31]) (count1261 q) 1 2 (meaningNeg28 q) (meaning1260 q) (meaning1263 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1260 = false ∨ valuation q 1263 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1264)) (countLit q [-36]) (countLit q [-38]) (count1264 q) 1 (meaningNeg38 q) (meaning1264 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1264 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1264)) (countLit q [-36]) (countLit q [-38]) (count1264 q) 1 (meaningNeg36 q) (meaning1264 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1264 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1265 = true := by
  have hs : count1264 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1265)) (countLit q [-36]) (countLit q [-38]) (count1264 q) 1 1 (meaningNeg36 q) (meaningNeg38 q) (meaning1265 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 38 = true ∨ valuation q 1265 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-33]) + (countLit q [-36, -38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-36, -38])
  have hm := merge_right (literal (valuationOf q) (1264)) (literal (valuationOf q) (1266)) (countLit q [-33]) (countLit q [-36, -38]) (count1266 q) 1 (meaning1264 q) (meaning1266 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1266 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1267 = true := by
  have hs : count1266 q = (countLit q [-33]) + (countLit q [-36, -38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-36, -38])
  have hm := merge_right (literal (valuationOf q) (1265)) (literal (valuationOf q) (1267)) (countLit q [-33]) (countLit q [-36, -38]) (count1266 q) 2 (meaning1265 q) (meaning1267 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1267 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-33]) + (countLit q [-36, -38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-36, -38])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1266)) (countLit q [-33]) (countLit q [-36, -38]) (count1266 q) 1 (meaningNeg33 q) (meaning1266 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1266 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1264 = false ∨ valuationOf q 1267 = true := by
  have hs : count1266 q = (countLit q [-33]) + (countLit q [-36, -38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-36, -38])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1267)) (countLit q [-33]) (countLit q [-36, -38]) (count1266 q) 1 1 (meaningNeg33 q) (meaning1264 q) (meaning1267 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1264 = false ∨ valuation q 1267 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1269 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_right (literal (valuationOf q) (1266)) (literal (valuationOf q) (1269)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 1 (meaning1266 q) (meaning1269 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1269 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1270 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_right (literal (valuationOf q) (1267)) (literal (valuationOf q) (1270)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 2 (meaning1267 q) (meaning1270 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1270 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1269 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_left (literal (valuationOf q) (1261)) (literal (valuationOf q) (1269)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 1 (meaning1261 q) (meaning1269 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1269 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1270 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_two (literal (valuationOf q) (1261)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1270)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 1 1 (meaning1261 q) (meaning1266 q) (meaning1270 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1266 = false ∨ valuation q 1270 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1271 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_two (literal (valuationOf q) (1261)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1271)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 1 2 (meaning1261 q) (meaning1267 q) (meaning1271 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1267 = false ∨ valuation q 1271 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1270 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_left (literal (valuationOf q) (1262)) (literal (valuationOf q) (1270)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 2 (meaning1262 q) (meaning1270 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1270 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1271 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1271)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 2 1 (meaning1262 q) (meaning1266 q) (meaning1271 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1266 = false ∨ valuation q 1271 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1271 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_left (literal (valuationOf q) (1263)) (literal (valuationOf q) (1271)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 3 (meaning1263 q) (meaning1271 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1271 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1272 = true := by
  have hs : count1269 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -36, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -36, -38])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1272)) (countLit q [-28, -29, -31]) (countLit q [-33, -36, -38]) (count1269 q) 3 1 (meaning1263 q) (meaning1266 q) (meaning1272 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1266 = false ∨ valuation q 1272 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-41]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1275)) (countLit q [-41]) (countLit q [-44]) (count1275 q) 1 (meaningNeg44 q) (meaning1275 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1275 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-41]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1275)) (countLit q [-41]) (countLit q [-44]) (count1275 q) 1 (meaningNeg41 q) (meaning1275 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1275 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-40]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41, -44])
  have hm := merge_right (literal (valuationOf q) (1275)) (literal (valuationOf q) (1277)) (countLit q [-40]) (countLit q [-41, -44]) (count1277 q) 1 (meaning1275 q) (meaning1277 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1277 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-40]) + (countLit q [-41, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41, -44])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1277)) (countLit q [-40]) (countLit q [-41, -44]) (count1277 q) 1 (meaningNeg40 q) (meaning1277 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1277 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1280)) (countLit q [-45]) (countLit q [-47]) (count1280 q) 1 (meaningNeg47 q) (meaning1280 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1280 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1280)) (countLit q [-45]) (countLit q [-47]) (count1280 q) 1 (meaningNeg45 q) (meaning1280 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1280 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1282 = true := by
  have hs : count1282 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1282)) (countLit q [-49]) (countLit q [-52]) (count1282 q) 1 (meaningNeg52 q) (meaning1282 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1282 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1282 = true := by
  have hs : count1282 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1282)) (countLit q [-49]) (countLit q [-52]) (count1282 q) 1 (meaningNeg49 q) (meaning1282 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1282 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1283 = true := by
  have hs : count1282 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1283)) (countLit q [-49]) (countLit q [-52]) (count1282 q) 1 1 (meaningNeg49 q) (meaningNeg52 q) (meaning1283 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 1283 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 1282 = false ∨ valuationOf q 1284 = true := by
  have hs : count1284 q = (countLit q [-45, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -52])
  have hm := merge_right (literal (valuationOf q) (1282)) (literal (valuationOf q) (1284)) (countLit q [-45, -47]) (countLit q [-49, -52]) (count1284 q) 1 (meaning1282 q) (meaning1284 q) hs
  change valuationOf q 1282 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 1282 = false ∨ valuation q 1284 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1285 = true := by
  have hs : count1284 q = (countLit q [-45, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -52])
  have hm := merge_right (literal (valuationOf q) (1283)) (literal (valuationOf q) (1285)) (countLit q [-45, -47]) (countLit q [-49, -52]) (count1284 q) 2 (meaning1283 q) (meaning1285 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1285 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1284 = true := by
  have hs : count1284 q = (countLit q [-45, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -52])
  have hm := merge_left (literal (valuationOf q) (1280)) (literal (valuationOf q) (1284)) (countLit q [-45, -47]) (countLit q [-49, -52]) (count1284 q) 1 (meaning1280 q) (meaning1284 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1284 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1285 = true := by
  have hs : count1284 q = (countLit q [-45, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -52])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1285)) (countLit q [-45, -47]) (countLit q [-49, -52]) (count1284 q) 1 1 (meaning1280 q) (meaning1282 q) (meaning1285 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1282 = false ∨ valuation q 1285 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true := by
  have hs : count1284 q = (countLit q [-45, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-49, -52])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1286)) (countLit q [-45, -47]) (countLit q [-49, -52]) (count1284 q) 1 2 (meaning1280 q) (meaning1283 q) (meaning1286 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1283 = false ∨ valuation q 1286 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E094.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112094
