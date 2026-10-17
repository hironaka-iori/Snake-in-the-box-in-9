import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_left (literal (valuationOf q) (1322)) (literal (valuationOf q) (1326)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1326 q) 1 (meaning1322 q) (meaning1326 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1326 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -47, -49, -52])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1330)) (countLit q [-40, -42, -44]) (countLit q [-46, -47, -49, -52]) (count1330 q) 1 (meaning1326 q) (meaning1330 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1330 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1326)) (literal (valuationOf q) (1331)) (countLit q [-40, -42, -44]) (countLit q [-46, -47, -49, -52]) (count1330 q) 1 1 (meaning1319 q) (meaning1326 q) (meaning1331 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1326 = false ∨ valuation q 1331 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1338 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -33, -35, -37]) + (countLit q [-40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -35, -37]) (l₂ := [-40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1338)) (countLit q [-28, -29, -31, -33, -35, -37]) (countLit q [-40, -42, -44, -46, -47, -49, -52]) (count1337 q) 1 1 (meaning1311 q) (meaning1330 q) (meaning1338 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1330 = false ∨ valuation q 1338 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1339 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -33, -35, -37]) + (countLit q [-40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -35, -37]) (l₂ := [-40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1339)) (countLit q [-28, -29, -31, -33, -35, -37]) (countLit q [-40, -42, -44, -46, -47, -49, -52]) (count1337 q) 1 2 (meaning1311 q) (meaning1331 q) (meaning1339 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1331 = false ∨ valuation q 1339 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -33, -35, -37]) + (countLit q [-40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -35, -37]) (l₂ := [-40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1340)) (countLit q [-28, -29, -31, -33, -35, -37]) (countLit q [-40, -42, -44, -46, -47, -49, -52]) (count1337 q) 2 2 (meaning1312 q) (meaning1331 q) (meaning1340 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1331 = false ∨ valuation q 1340 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-28, -29, -31, -33, -35, -37]) + (countLit q [-40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -33, -35, -37]) (l₂ := [-40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1313)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1340)) (countLit q [-28, -29, -31, -33, -35, -37]) (countLit q [-40, -42, -44, -46, -47, -49, -52]) (count1337 q) 3 1 (meaning1313 q) (meaning1330 q) (meaning1340 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1330 = false ∨ valuation q 1340 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1353 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) + (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (l₂ := [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1353)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (count1350 q) 2 2 (meaning1289 q) (meaning1338 q) (meaning1353 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1338 = false ∨ valuation q 1353 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) + (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (l₂ := [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1354)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (count1350 q) 2 3 (meaning1289 q) (meaning1339 q) (meaning1354 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1339 = false ∨ valuation q 1354 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) + (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (l₂ := [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1355)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (count1350 q) 2 4 (meaning1289 q) (meaning1340 q) (meaning1355 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1340 = false ∨ valuation q 1355 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) + (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (l₂ := [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1354)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (count1350 q) 3 2 (meaning1290 q) (meaning1338 q) (meaning1354 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1338 = false ∨ valuation q 1354 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) + (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (l₂ := [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1355)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (count1350 q) 3 3 (meaning1290 q) (meaning1339 q) (meaning1355 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1339 = false ∨ valuation q 1355 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) + (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (l₂ := [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1355)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (count1350 q) 4 2 (meaning1291 q) (meaning1338 q) (meaning1355 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1338 = false ∨ valuation q 1355 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) + (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (l₂ := [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1356)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -18, -20, -21, -23, -26]) (countLit q [-28, -29, -31, -33, -35, -37, -40, -42, -44, -46, -47, -49, -52]) (count1350 q) 4 3 (meaning1291 q) (meaning1339 q) (meaning1356 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1339 = false ∨ valuation q 1356 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1363)) (countLit q [-55]) (countLit q [-57]) (count1363 q) 1 (meaningNeg55 q) (meaning1363 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1363 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-54]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -57])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1365)) (countLit q [-54]) (countLit q [-55, -57]) (count1365 q) 1 (meaning1363 q) (meaning1365 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1365 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (1368)) (countLit q [-61]) (countLit q [-64]) (count1368 q) 1 (meaningNeg64 q) (meaning1368 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1368 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1368)) (countLit q [-61]) (countLit q [-64]) (count1368 q) 1 (meaningNeg61 q) (meaning1368 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1368 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 64 = true ∨ valuationOf q 1369 = true := by
  have hs : count1368 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (1369)) (countLit q [-61]) (countLit q [-64]) (count1368 q) 1 1 (meaningNeg61 q) (meaningNeg64 q) (meaning1369 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 1369 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -64])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1370)) (countLit q [-60]) (countLit q [-61, -64]) (count1370 q) 1 (meaning1368 q) (meaning1370 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1370 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -64])
  have hm := merge_right (literal (valuationOf q) (1369)) (literal (valuationOf q) (1371)) (countLit q [-60]) (countLit q [-61, -64]) (count1370 q) 2 (meaning1369 q) (meaning1371 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1371 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -64])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1370)) (countLit q [-60]) (countLit q [-61, -64]) (count1370 q) 1 (meaningNeg60 q) (meaning1370 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1370 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1371)) (countLit q [-60]) (countLit q [-61, -64]) (count1370 q) 1 1 (meaningNeg60 q) (meaning1368 q) (meaning1371 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1368 = false ∨ valuation q 1371 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1369 = false ∨ valuationOf q 1372 = true := by
  have hs : count1370 q = (countLit q [-60]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1372)) (countLit q [-60]) (countLit q [-61, -64]) (count1370 q) 1 2 (meaningNeg60 q) (meaning1369 q) (meaning1372 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1369 = false ∨ valuation q 1372 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-54, -55, -57]) + (countLit q [-60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-60, -61, -64])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1373)) (countLit q [-54, -55, -57]) (countLit q [-60, -61, -64]) (count1373 q) 1 (meaning1370 q) (meaning1373 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1373 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-54, -55, -57]) + (countLit q [-60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-60, -61, -64])
  have hm := merge_right (literal (valuationOf q) (1371)) (literal (valuationOf q) (1374)) (countLit q [-54, -55, -57]) (countLit q [-60, -61, -64]) (count1373 q) 2 (meaning1371 q) (meaning1374 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1374 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-54, -55, -57]) + (countLit q [-60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-60, -61, -64])
  have hm := merge_right (literal (valuationOf q) (1372)) (literal (valuationOf q) (1375)) (countLit q [-54, -55, -57]) (countLit q [-60, -61, -64]) (count1373 q) 3 (meaning1372 q) (meaning1375 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1375 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-54, -55, -57]) + (countLit q [-60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-60, -61, -64])
  have hm := merge_left (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-54, -55, -57]) (countLit q [-60, -61, -64]) (count1373 q) 1 (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1373 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-54, -55, -57]) + (countLit q [-60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1374)) (countLit q [-54, -55, -57]) (countLit q [-60, -61, -64]) (count1373 q) 1 1 (meaning1365 q) (meaning1370 q) (meaning1374 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1370 = false ∨ valuation q 1374 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1379)) (countLit q [-67]) (countLit q [-70]) (count1379 q) 1 (meaningNeg70 q) (meaning1379 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1379 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1379)) (countLit q [-67]) (countLit q [-70]) (count1379 q) 1 (meaningNeg67 q) (meaning1379 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1379 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1380 = true := by
  have hs : count1379 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1380)) (countLit q [-67]) (countLit q [-70]) (count1379 q) 1 1 (meaningNeg67 q) (meaningNeg70 q) (meaning1380 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 1380 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E246.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112246
