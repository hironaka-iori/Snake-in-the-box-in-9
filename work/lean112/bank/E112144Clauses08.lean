import E112144Semantics
import B112E144Inputs
namespace Snake9.Regrowth.E112144
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (1319)) (literal (valuationOf q) (1330)) (countLit q [-40, -43, -45]) (countLit q [-46, -47, -50, -52]) (count1330 q) 1 (meaning1319 q) (meaning1330 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1330 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1326)) (literal (valuationOf q) (1331)) (countLit q [-40, -43, -45]) (countLit q [-46, -47, -50, -52]) (count1330 q) 1 1 (meaning1319 q) (meaning1326 q) (meaning1331 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1326 = false ∨ valuation q 1331 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1332 = true := by
  have hs : count1330 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1332)) (countLit q [-40, -43, -45]) (countLit q [-46, -47, -50, -52]) (count1330 q) 1 2 (meaning1319 q) (meaning1327 q) (meaning1332 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1327 = false ∨ valuation q 1332 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (1320)) (literal (valuationOf q) (1331)) (countLit q [-40, -43, -45]) (countLit q [-46, -47, -50, -52]) (count1330 q) 2 (meaning1320 q) (meaning1331 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1331 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1332 = true := by
  have hs : count1330 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1326)) (literal (valuationOf q) (1332)) (countLit q [-40, -43, -45]) (countLit q [-46, -47, -50, -52]) (count1330 q) 2 1 (meaning1320 q) (meaning1326 q) (meaning1332 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1326 = false ∨ valuation q 1332 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1333 = true := by
  have hs : count1330 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1333)) (countLit q [-40, -43, -45]) (countLit q [-46, -47, -50, -52]) (count1330 q) 2 2 (meaning1320 q) (meaning1327 q) (meaning1333 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1327 = false ∨ valuation q 1333 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -34, -35, -37]) + (countLit q [-40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -37]) (l₂ := [-40, -43, -45, -46, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1330)) (literal (valuationOf q) (1337)) (countLit q [-28, -29, -31, -34, -35, -37]) (countLit q [-40, -43, -45, -46, -47, -50, -52]) (count1337 q) 1 (meaning1330 q) (meaning1337 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1337 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1338 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -34, -35, -37]) + (countLit q [-40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -37]) (l₂ := [-40, -43, -45, -46, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1331)) (literal (valuationOf q) (1338)) (countLit q [-28, -29, -31, -34, -35, -37]) (countLit q [-40, -43, -45, -46, -47, -50, -52]) (count1337 q) 2 (meaning1331 q) (meaning1338 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1338 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -34, -35, -37]) + (countLit q [-40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -37]) (l₂ := [-40, -43, -45, -46, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (1311)) (literal (valuationOf q) (1337)) (countLit q [-28, -29, -31, -34, -35, -37]) (countLit q [-40, -43, -45, -46, -47, -50, -52]) (count1337 q) 1 (meaning1311 q) (meaning1337 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1337 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1338 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -34, -35, -37]) + (countLit q [-40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -37]) (l₂ := [-40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1338)) (countLit q [-28, -29, -31, -34, -35, -37]) (countLit q [-40, -43, -45, -46, -47, -50, -52]) (count1337 q) 1 1 (meaning1311 q) (meaning1330 q) (meaning1338 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1330 = false ∨ valuation q 1338 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1339 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -34, -35, -37]) + (countLit q [-40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -37]) (l₂ := [-40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1339)) (countLit q [-28, -29, -31, -34, -35, -37]) (countLit q [-40, -43, -45, -46, -47, -50, -52]) (count1337 q) 1 2 (meaning1311 q) (meaning1331 q) (meaning1339 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1331 = false ∨ valuation q 1339 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -34, -35, -37]) + (countLit q [-40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -37]) (l₂ := [-40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1340)) (countLit q [-28, -29, -31, -34, -35, -37]) (countLit q [-40, -43, -45, -46, -47, -50, -52]) (count1337 q) 1 3 (meaning1311 q) (meaning1332 q) (meaning1340 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1332 = false ∨ valuation q 1340 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1341 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -34, -35, -37]) + (countLit q [-40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -37]) (l₂ := [-40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1341)) (countLit q [-28, -29, -31, -34, -35, -37]) (countLit q [-40, -43, -45, -46, -47, -50, -52]) (count1337 q) 1 4 (meaning1311 q) (meaning1333 q) (meaning1341 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1333 = false ∨ valuation q 1341 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1354)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 2 3 (meaning1289 q) (meaning1339 q) (meaning1354 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1339 = false ∨ valuation q 1354 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1355)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 2 4 (meaning1289 q) (meaning1340 q) (meaning1355 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1340 = false ∨ valuation q 1355 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1356)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 2 5 (meaning1289 q) (meaning1341 q) (meaning1356 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1341 = false ∨ valuation q 1356 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1353 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1353)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 3 1 (meaning1290 q) (meaning1337 q) (meaning1353 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1337 = false ∨ valuation q 1353 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1354)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 3 2 (meaning1290 q) (meaning1338 q) (meaning1354 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1338 = false ∨ valuation q 1354 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1355)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 3 3 (meaning1290 q) (meaning1339 q) (meaning1355 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1339 = false ∨ valuation q 1355 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1356)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 3 4 (meaning1290 q) (meaning1340 q) (meaning1356 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1340 = false ∨ valuation q 1356 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1354)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 4 1 (meaning1291 q) (meaning1337 q) (meaning1354 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1337 = false ∨ valuation q 1354 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1355)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 4 2 (meaning1291 q) (meaning1338 q) (meaning1355 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1338 = false ∨ valuation q 1355 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1357 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1357)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 4 4 (meaning1291 q) (meaning1340 q) (meaning1357 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1340 = false ∨ valuation q 1357 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1355)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 5 1 (meaning1292 q) (meaning1337 q) (meaning1355 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1337 = false ∨ valuation q 1355 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1356)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 5 2 (meaning1292 q) (meaning1338 q) (meaning1356 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1338 = false ∨ valuation q 1356 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1356)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 6 1 (meaning1293 q) (meaning1337 q) (meaning1356 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1337 = false ∨ valuation q 1356 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1357 = true := by
  have hs : count1350 q = (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) + (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (l₂ := [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1357)) (countLit q [-1, -2, -5, -7, -9, -11, -12, -14, -17, -19, -20, -23, -26]) (countLit q [-28, -29, -31, -34, -35, -37, -40, -43, -45, -46, -47, -50, -52]) (count1350 q) 6 2 (meaning1293 q) (meaning1338 q) (meaning1357 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1338 = false ∨ valuation q 1357 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1363)) (countLit q [-56]) (countLit q [-58]) (count1363 q) 1 (meaningNeg56 q) (meaning1363 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1363 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1364 = true := by
  have hs : count1363 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1364)) (countLit q [-56]) (countLit q [-58]) (count1363 q) 1 1 (meaningNeg56 q) (meaningNeg58 q) (meaning1364 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 58 = true ∨ valuation q 1364 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1365)) (countLit q [-54]) (countLit q [-56, -58]) (count1365 q) 1 (meaning1363 q) (meaning1365 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1365 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (1364)) (literal (valuationOf q) (1366)) (countLit q [-54]) (countLit q [-56, -58]) (count1365 q) 2 (meaning1364 q) (meaning1366 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1366 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1363 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1366)) (countLit q [-54]) (countLit q [-56, -58]) (count1365 q) 1 1 (meaningNeg54 q) (meaning1363 q) (meaning1366 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1363 = false ∨ valuation q 1366 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E144.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112144
